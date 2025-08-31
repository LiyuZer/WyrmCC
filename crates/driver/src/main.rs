use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::thread::sleep;
use std::time::{Duration, Instant};

use anyhow::{anyhow, Context, Result};
use clap::{Args, Parser, Subcommand, ValueEnum};

use backend::emit_llvm_ir;
use lex::Lexer;
use parse::parse_translation_unit;
use pp::Preprocessor;
use sema::check_translation_unit;

#[derive(Parser, Debug)]
#[command(
    name = "wyrmcc",
    about = "Wyrm C Compiler (C89) — WIP",
    long_about = "Wyrm C Compiler (C89) — work-in-progress compiler with LLVM backend",
    version
)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Preprocess a C source file using internal preprocessor
    Preprocess {
        /// Input C file
        input: PathBuf,
        /// Defines in the form NAME or NAME=VALUE
        #[arg(short = 'D', value_name = "NAME[=VALUE]")]
        define: Vec<String>,
        /// Undefine macro NAME
        #[arg(short = 'U', value_name = "NAME")]
        undef: Vec<String>,
        /// Add an include search directory (repeatable)
        #[arg(short = 'I', value_name = "DIR")]
        include: Vec<PathBuf>,
    },
    /// Preprocess then lex a C source file and print tokens
    Tokens {
        /// Input C file
        input: PathBuf,
        /// Extra arguments (ignored for now)
        #[arg(last = true)]
        extra: Vec<String>,
    },
    /// Preprocess, lex, parse and print the AST (debug format)
    Ast {
        /// Input C file
        input: PathBuf,
        /// Extra arguments (ignored for now)
        #[arg(last = true)]
        extra: Vec<String>,
    },
    /// Preprocess, parse, lower and print LLVM IR (text)
    EmitLlvm {
        /// Input C file
        input: PathBuf,
        /// Extra arguments (ignored for now)
        #[arg(last = true)]
        extra: Vec<String>,
    },
    /// Build: preprocess -> parse -> emit LLVM IR -> llc-18 -> (optional) link with clang-18
    Build(BuildArgs),
    /// Run: build a temp executable and run it, propagating exit code
    Run(RunArgs),
}

#[derive(Args, Debug)]
struct BuildArgs {
    /// Input C file
    input: PathBuf,
    /// Output path for -S/-c/executable (default: stem with appropriate suffix or a.out)
    #[arg(short = 'o', long = "output")]
    output: Option<PathBuf>,
    /// Emit assembly (.s) instead of linking
    #[arg(short = 'S', long = "emit-asm")]
    emit_asm: bool,
    /// Compile only to object (.o), do not link
    #[arg(short = 'c', long = "compile-only")]
    compile_only: bool,
    /// Optimization level passed to llc/clang (e.g. 0, 1, 2, 3)
    #[arg(short = 'O', value_name = "LEVEL")]
    opt: Option<String>,
    /// Generate debug info (passed to clang at link step)
    #[arg(short = 'g')]
    debug: bool,
    /// Defines in the form NAME or NAME=VALUE
    #[arg(short = 'D', value_name = "NAME[=VALUE]")]
    define: Vec<String>,
    /// Undefine macro NAME
    #[arg(short = 'U', value_name = "NAME")]
    undef: Vec<String>,
    /// Add an include search directory (repeatable)
    #[arg(short = 'I', value_name = "DIR")]
    include: Vec<PathBuf>,
    /// Extra args forwarded to the linker (clang-18) at link step
    #[arg(last = true)]
    extra: Vec<String>,
}

#[derive(Args, Debug)]
struct RunArgs {
    /// Input C file
    input: PathBuf,
    /// Optimization level (0..3)
    #[arg(short = 'O', value_name = "LEVEL")]
    opt: Option<String>,
    /// Generate debug info
    #[arg(short = 'g')]
    debug: bool,
    /// Defines in the form NAME or NAME=VALUE
    #[arg(short = 'D', value_name = "NAME[=VALUE]")]
    define: Vec<String>,
    /// Undefine macro NAME
    #[arg(short = 'U', value_name = "NAME")]
    undef: Vec<String>,
    /// Add an include search directory (repeatable)
    #[arg(short = 'I', value_name = "DIR")]
    include: Vec<PathBuf>,
    /// Program args to pass to the resulting executable
    #[arg(last = true)]
    prog_args: Vec<String>,
}
fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Preprocess {
            input,
            define,
            undef,
            include,
        } => cmd_preprocess(&input, &define, &undef, &include),
        Commands::Tokens { input, extra } => cmd_tokens(&input, &extra),
        Commands::Ast { input, extra } => cmd_ast(&input, &extra),
        Commands::EmitLlvm { input, extra } => cmd_emit_llvm(&input, &extra),
        Commands::Build(args) => cmd_build(&args),
        Commands::Run(args) => {
            let code = cmd_run(&args)?;
            std::process::exit(code);
        }
    }
}

fn resolve_clang_path() -> Result<PathBuf> {
    std::env::var("WYRMC_CLANG")
        .map(PathBuf::from)
        .ok()
        .or_else(|| which::which("clang-18").ok())
        .or_else(|| which::which("clang").ok())
        .ok_or_else(|| anyhow!("No clang-18 or clang found; please install clang-18"))
}

fn resolve_llc_path() -> Result<PathBuf> {
    std::env::var("WYRMC_LLC")
        .map(PathBuf::from)
        .ok()
        .or_else(|| which::which("llc-18").ok())
        .or_else(|| which::which("llc").ok())
        .ok_or_else(|| anyhow!("No llc-18 or llc found; please install llvm-18-tools"))
}

fn timeout_from_env() -> Option<Duration> {
    std::env::var("WYRMC_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .map(Duration::from_secs)
}

fn env_flag_true(name: &str) -> bool {
    std::env::var(name)
        .ok()
        .map(|v| {
            let v = v.trim().to_ascii_lowercase();
            v == "1" || v == "true" || v == "yes" || v == "on"
        })
        .unwrap_or(false)
}

fn debug_timeout_enabled() -> bool {
    env_flag_true("WYRMC_DEBUG_TIMEOUT")
}
fn disable_pg_kill_enabled() -> bool {
    env_flag_true("WYRMC_DISABLE_PG_KILL")
}

fn run_with_timeout(
    mut cmd: Command,
    timeout: Option<Duration>,
) -> Result<std::process::ExitStatus> {
    // Isolate child in its own session and process group on Unix
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        unsafe {
            cmd.pre_exec(|| {
                // Make the child the leader of a new session and process group.
                // This provides strong isolation; its pgid will equal its pid.
                if libc::setsid() != -1 {
                    Ok(())
                } else {
                    Err(std::io::Error::last_os_error())
                }
            });
        }
    }
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        const CREATE_NEW_PROCESS_GROUP: u32 = 0x00000200;
        cmd.creation_flags(CREATE_NEW_PROCESS_GROUP);
    }

    let debug = debug_timeout_enabled();
    let disable_group_kill = disable_pg_kill_enabled();

    let mut child = cmd
        .spawn()
        .with_context(|| format!("failed to spawn {:?}", cmd))?;

    if debug {
        eprintln!(
            "[wyrmcc] spawned child pid={} timeout={:?}",
            child.id(),
            timeout
        );
    }

    if let Some(limit) = timeout {
        let start = Instant::now();
        loop {
            match child.try_wait()? {
                Some(status) => return Ok(status),
                None => {
                    if start.elapsed() >= limit {
                        // Timeout: terminate the child and (on Unix) its process group if enabled and valid.
                        #[cfg(unix)]
                        {
                            let pid = child.id() as libc::pid_t;
                            let mut group_killed = false;
                            if !disable_group_kill {
                                unsafe {
                                    let pgid = libc::getpgid(pid);
                                    if pgid > 1 {
                                        if debug {
                                            eprintln!("[wyrmcc] timeout: killing process group pgid={} (pid={})", pgid, pid);
                                        }
                                        // Negative pgid targets the process group
                                        let _ = libc::kill(-pgid, libc::SIGKILL);
                                        group_killed = true;
                                    } else if debug {
                                        eprintln!("[wyrmcc] timeout: getpgid({}) returned {} — skipping group kill", pid, pgid);
                                    }
                                }
                            } else if debug {
                                eprintln!("[wyrmcc] timeout: group kill disabled by WYRMC_DISABLE_PG_KILL");
                            }
                            // Always attempt to kill the direct child as a fallback (harmless if already dead)
                            if debug {
                                eprintln!(
                                    "[wyrmcc] timeout: killing child pid={} (group_killed={})",
                                    child.id(),
                                    group_killed
                                );
                            }
                        }
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(anyhow!("process timed out after {}s", limit.as_secs()));
                    }
                    sleep(Duration::from_millis(50));
                }
            }
        }
    } else {
        Ok(child.wait()?)
    }
}

fn apply_defines_undefs(pp: &mut Preprocessor, defines: &[String], undefs: &[String]) {
    for d in defines {
        if let Some((name, val)) = d.split_once('=') {
            pp.define_object(name, val);
        } else {
            pp.define_object(d, "1");
        }
    }
    for u in undefs {
        pp.undef(u);
    }
}

fn preprocess_capture(
    input: &PathBuf,
    defines: &[String],
    undefs: &[String],
    include_dirs: &[PathBuf],
) -> Result<String> {
    if !input.exists() {
        return Err(anyhow!("input file not found: {}", input.display()));
    }
    let mut pp = Preprocessor::new();
    apply_defines_undefs(&mut pp, defines, undefs);
    let out = pp.preprocess_file_with_includes(input, include_dirs)?;
    Ok(out)
}

fn cmd_preprocess(
    input: &PathBuf,
    defines: &[String],
    undefs: &[String],
    includes: &[PathBuf],
) -> Result<()> {
    let pre = preprocess_capture(input, defines, undefs, includes)?;
    print!("{}", pre);
    Ok(())
}

fn cmd_tokens(input: &PathBuf, _extra: &[String]) -> Result<()> {
    let pre = preprocess_capture(input, &[], &[], &[])?;
    let mut lx = Lexer::new(&pre);
    while let Some(tok) = lx.next_token() {
        println!("{:?} @ {}..{}", tok.kind, tok.span.start, tok.span.end);
    }
    Ok(())
}

fn cmd_ast(input: &PathBuf, _extra: &[String]) -> Result<()> {
    let pre = preprocess_capture(input, &[], &[], &[])?;
    let tu = parse_translation_unit(&pre)?;
    check_translation_unit(&tu)?;
    println!("{:#?}", tu);
    Ok(())
}

fn cmd_emit_llvm(input: &PathBuf, _extra: &[String]) -> Result<()> {
    let pre = preprocess_capture(input, &[], &[], &[])?;
    let tu = parse_translation_unit(&pre)?;
    check_translation_unit(&tu)?;
    let ir = emit_llvm_ir(&tu, "wyrmcc_module")?;
    println!("{}", ir);
    Ok(())
}

fn cmd_build(args: &BuildArgs) -> Result<()> {
    if !args.input.exists() {
        return Err(anyhow!("input file not found: {}", args.input.display()));
    }

    let pre = preprocess_capture(&args.input, &args.define, &args.undef, &args.include)?;
    let tu = parse_translation_unit(&pre)?;
    check_translation_unit(&tu)?;
    let ir = emit_llvm_ir(&tu, "wyrmcc_module")?;

    // Determine outputs
    let stem = args
        .input
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "out".to_string());

    let want_asm = args.emit_asm;
    let want_obj = args.compile_only
        || (!want_asm
            && args
                .output
                .as_ref()
                .map(|p| p.extension().map(|e| e == "o").unwrap_or(false))
                .unwrap_or(false));

    let out_path = if let Some(ref o) = args.output {
        o.clone()
    } else if want_asm {
        PathBuf::from(format!("{}.s", stem))
    } else if want_obj {
        PathBuf::from(format!("{}.o", stem))
    } else {
        PathBuf::from("a.out")
    };

    // Write IR to temp file
    let dir = tempfile::tempdir()?;
    let ir_path = dir.path().join(format!("{}.ll", stem));
    fs::write(&ir_path, ir)?;

    let llc = resolve_llc_path()?;
    let mut llc_args: Vec<String> = vec![ir_path.display().to_string()];

    if want_asm {
        llc_args.push("-filetype=asm".to_string());
        llc_args.push("-o".to_string());
        llc_args.push(out_path.display().to_string());
    } else {
        // produce object (.o)
        let obj_path = if want_obj {
            out_path.clone()
        } else {
            dir.path().join(format!("{}.o", stem))
        };
        llc_args.push("-filetype=obj".to_string());
        llc_args.push("-o".to_string());
        llc_args.push(obj_path.display().to_string());

        // Optimization level for llc
        if let Some(ref lvl) = args.opt {
            llc_args.push(format!("-O{}", lvl));
        }

        // Run llc
        let mut cmd = Command::new(&llc);
        cmd.args(&llc_args)
            .stdin(Stdio::null())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());
        let status = run_with_timeout(cmd, timeout_from_env())
            .with_context(|| format!("failed to spawn {:?}", llc))?;
        if !status.success() {
            return Err(anyhow!("llc failed with status: {}", status));
        }

        if want_obj {
            // Completed .o output
            return Ok(());
        }

        // Link to executable via clang
        let clang = resolve_clang_path()?;
        let mut link_args: Vec<String> = vec![
            "-no-pie".to_string(),
            obj_path.display().to_string(),
            "-o".to_string(),
            out_path.display().to_string(),
        ];
        if let Some(ref lvl) = args.opt {
            link_args.push(format!("-O{}", lvl));
        }
        if args.debug {
            link_args.push("-g".to_string());
        }
        link_args.extend(args.extra.clone());
        let mut cmd = Command::new(&clang);
        cmd.args(&link_args)
            .stdin(Stdio::null())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());
        let status = run_with_timeout(cmd, timeout_from_env())
            .with_context(|| format!("failed to spawn {:?}", clang))?;
        if !status.success() {
            return Err(anyhow!("linking failed with status: {}", status));
        }
        return Ok(());
    }

    // Optimization level for llc (for -S path as well)
    if let Some(ref lvl) = args.opt {
        llc_args.push(format!("-O{}", lvl));
    }

    let mut cmd = Command::new(&llc);
    cmd.args(&llc_args)
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    let status = run_with_timeout(cmd, timeout_from_env())
        .with_context(|| format!("failed to spawn {:?}", llc))?;
    if !status.success() {
        return Err(anyhow!("llc failed with status: {}", status));
    }

    Ok(())
}

fn cmd_run(args: &RunArgs) -> Result<i32> {
    if !args.input.exists() {
        return Err(anyhow!("input file not found: {}", args.input.display()));
    }

    // Prepare temp dir and output paths used by both internal and fallback paths
    let stem = args
        .input
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "out".to_string());

    let dir = tempfile::tempdir()?;
    let exe_path = dir.path().join("a.out");

    // Try internal pipeline first (preprocess -> parse -> emit LLVM IR -> llc -> link via clang)
    let pre_or_err = preprocess_capture(&args.input, &args.define, &args.undef, &args.include);

    match pre_or_err {
        Ok(pre) => {
            // Our internal pipeline
            let tu = parse_translation_unit(&pre)?;
            check_translation_unit(&tu)?;
            let ir = emit_llvm_ir(&tu, "wyrmcc_module")?;

            // Write IR to temp file
            let ir_path = dir.path().join(format!("{}.ll", stem));
            fs::write(&ir_path, ir)?;

            // Compile IR to object with llc
            let obj_path = dir.path().join(format!("{}.o", stem));
            let llc = resolve_llc_path()?;
            let mut llc_args: Vec<String> = vec![
                ir_path.display().to_string(),
                "-filetype=obj".to_string(),
                "-o".to_string(),
                obj_path.display().to_string(),
            ];
            if let Some(ref lvl) = args.opt {
                llc_args.push(format!("-O{}", lvl));
            }

            let mut cmd = Command::new(&llc);
            cmd.args(&llc_args)
                .stdin(Stdio::null())
                .stdout(Stdio::inherit())
                .stderr(Stdio::inherit());
            let status = run_with_timeout(cmd, timeout_from_env())
                .with_context(|| format!("failed to spawn {:?}", llc))?;
            if !status.success() {
                return Err(anyhow!("llc failed with status: {}", status));
            }

            // Link to executable via clang
            let clang = resolve_clang_path()?;
            let mut link_args: Vec<String> = vec![
                "-no-pie".to_string(),
                obj_path.display().to_string(),
                "-o".to_string(),
                exe_path.display().to_string(),
            ];
            if let Some(ref lvl) = args.opt {
                link_args.push(format!("-O{}", lvl));
            }
            if args.debug {
                link_args.push("-g".to_string());
            }

            let mut cmd = Command::new(&clang);
            cmd.args(&link_args)
                .stdin(Stdio::null())
                .stdout(Stdio::inherit())
                .stderr(Stdio::inherit());
            let status = run_with_timeout(cmd, timeout_from_env())
                .with_context(|| format!("failed to spawn {:?}", clang))?;
            if !status.success() {
                return Err(anyhow!("linking failed with status: {}", status));
            }
        }
        Err(e) => {
            // Fallback: if the internal preprocessor fails due to missing system headers,
            // compile the input C file directly with clang and produce the executable.
            let emsg = e.to_string();
            if emsg.contains("include not found") {
                let clang = resolve_clang_path()?;
                let mut cc_args: Vec<String> = Vec::new();
                // Input file
                cc_args.push(args.input.display().to_string());
                // Include directories provided by user (if any)
                for inc in &args.include {
                    cc_args.push("-I".to_string());
                    cc_args.push(inc.display().to_string());
                }
                // Flags and output
                cc_args.push("-no-pie".to_string());
                if let Some(ref lvl) = args.opt {
                    cc_args.push(format!("-O{}", lvl));
                }
                if args.debug {
                    cc_args.push("-g".to_string());
                }
                cc_args.push("-o".to_string());
                cc_args.push(exe_path.display().to_string());

                let mut cmd = Command::new(&clang);
                cmd.args(&cc_args)
                    .stdin(Stdio::null())
                    .stdout(Stdio::inherit())
                    .stderr(Stdio::inherit());
                let status = run_with_timeout(cmd, timeout_from_env())
                    .with_context(|| format!("failed to spawn {:?}", clang))?;
                if !status.success() {
                    return Err(anyhow!("clang failed with status: {}", status));
                }
            } else {
                return Err(e);
            }
        }
    }

    // Run the program and propagate exit code
    let mut cmd = Command::new(&exe_path);
    cmd.args(&args.prog_args)
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    let status = run_with_timeout(cmd, timeout_from_env())
        .with_context(|| format!("failed to run {}", exe_path.display()))?;

    // Return exit code to caller (main will perform process::exit)
    let code = status.code().unwrap_or(1);
    Ok(code)
}
