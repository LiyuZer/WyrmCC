use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use std::thread::sleep;

use anyhow::{anyhow, Context, Result};
use clap::{Parser, Subcommand, Args, ValueEnum};

use lex::Lexer;
use parse::parse_translation_unit;
use backend::emit_llvm_ir;
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
    /// Preprocess a C source file (bootstrap via clang -E)
    Preprocess {
        /// Input C file
        input: PathBuf,
        /// Extra arguments passed through to clang (placed after default flags)
        #[arg(last = true)]
        extra: Vec<String>,
    },
    /// Preprocess then lex a C source file and print tokens
    Tokens {
        /// Input C file
        input: PathBuf,
        /// Extra arguments passed through to clang (placed after default flags)
        #[arg(last = true)]
        extra: Vec<String>,
    },
    /// Preprocess, lex, parse and print the AST (debug format)
    Ast {
        /// Input C file
        input: PathBuf,
        /// Extra arguments passed through to clang (placed after default flags)
        #[arg(last = true)]
        extra: Vec<String>,
    },
    /// Preprocess, parse, lower and print LLVM IR (text)
    EmitLlvm {
        /// Input C file
        input: PathBuf,
        /// Extra arguments passed through to clang (placed after default flags)
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
    /// Program args to pass to the resulting executable
    #[arg(last = true)]
    prog_args: Vec<String>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Preprocess { input, extra } => cmd_preprocess(&input, &extra),
        Commands::Tokens { input, extra } => cmd_tokens(&input, &extra),
        Commands::Ast { input, extra } => cmd_ast(&input, &extra),
        Commands::EmitLlvm { input, extra } => cmd_emit_llvm(&input, &extra),
        Commands::Build(args) => cmd_build(&args),
        Commands::Run(args) => cmd_run(&args),
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

fn run_with_timeout(mut cmd: Command, timeout: Option<Duration>) -> Result<std::process::ExitStatus> {
    let mut child = cmd
        .spawn()
        .with_context(|| format!("failed to spawn {:?}", cmd))?;

    if let Some(limit) = timeout {
        let start = Instant::now();
        loop {
            match child.try_wait()? {
                Some(status) => return Ok(status),
                None => {
                    if start.elapsed() >= limit {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(anyhow!(
                            "process timed out after {}s",
                            limit.as_secs()
                        ));
                    }
                    sleep(Duration::from_millis(50));
                }
            }
        }
    } else {
        Ok(child.wait()?)
    }
}

fn cmd_preprocess(input: &PathBuf, extra: &[String]) -> Result<()> {
    if !input.exists() {
        return Err(anyhow!("input file not found: {}", input.display()));
    }

    let clang_path = resolve_clang_path()?;

    let mut args: Vec<String> = vec!["-E", "-P", "-std=c89", "-xc"]
        .into_iter()
        .map(String::from)
        .collect();
    args.push(input.display().to_string());
    args.extend(extra.iter().cloned());

    let mut cmd = Command::new(&clang_path);
    cmd.args(&args)
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());

    let status = run_with_timeout(cmd, timeout_from_env())
        .with_context(|| format!("failed to spawn {:?}", clang_path))?;

    if !status.success() {
        return Err(anyhow!(
            "clang preprocessing failed with status: {}",
            status
        ));
    }

    Ok(())
}

fn preprocess_capture(input: &PathBuf, extra: &[String]) -> Result<String> {
    if !input.exists() {
        return Err(anyhow!("input file not found: {}", input.display()));
    }

    let clang_path = resolve_clang_path()?;

    let mut args: Vec<String> = vec!["-E", "-P", "-std=c89", "-xc"]
        .into_iter()
        .map(String::from)
        .collect();
    args.push(input.display().to_string());
    args.extend(extra.iter().cloned());

    // For now we keep capture path without timeout; can be switched to a timed spawn if needed.
    let output = Command::new(&clang_path)
        .args(&args)
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .output()
        .with_context(|| format!("failed to spawn {:?}", clang_path))?;

    if !output.status.success() {
        return Err(anyhow!(
            "clang preprocessing failed with status: {}",
            output.status
        ));
    }

    let s = String::from_utf8(output.stdout)
        .context("preprocessor output was not valid UTF-8; expected text after -E -P")?;
    Ok(s)
}

fn cmd_tokens(input: &PathBuf, extra: &[String]) -> Result<()> {
    let pre = preprocess_capture(input, extra)?;
    let mut lx = Lexer::new(&pre);
    while let Some(tok) = lx.next_token() {
        println!("{:?} @ {}..{}", tok.kind, tok.span.start, tok.span.end);
    }
    Ok(())
}

fn cmd_ast(input: &PathBuf, extra: &[String]) -> Result<()> {
    let pre = preprocess_capture(input, extra)?;
    let tu = parse_translation_unit(&pre)?;
    check_translation_unit(&tu)?;
    println!("{:#?}", tu);
    Ok(())
}

fn cmd_emit_llvm(input: &PathBuf, extra: &[String]) -> Result<()> {
    let pre = preprocess_capture(input, extra)?;
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

    let pre = preprocess_capture(&args.input, &[])?;
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
    let want_obj = args.compile_only || (!want_asm && args.output.as_ref().map(|p| p.extension().map(|e| e == "o").unwrap_or(false)).unwrap_or(false));

    let out_path = if let Some(ref o) = args.output { o.clone() } else if want_asm { PathBuf::from(format!("{}.s", stem)) } else if want_obj { PathBuf::from(format!("{}.o", stem)) } else { PathBuf::from("a.out") };

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
        let obj_path = if want_obj { out_path.clone() } else { dir.path().join(format!("{}.o", stem)) };
        llc_args.push("-filetype=obj".to_string());
        llc_args.push("-o".to_string());
        llc_args.push(obj_path.display().to_string());

        // Optimization level for llc
        if let Some(ref lvl) = args.opt { llc_args.push(format!("-O{}", lvl)); }

        // Run llc
        let mut cmd = Command::new(&llc);
        cmd.args(&llc_args)
            .stdin(Stdio::null())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());
        let status = run_with_timeout(cmd, timeout_from_env())
            .with_context(|| format!("failed to spawn {:?}", llc))?;
        if !status.success() { return Err(anyhow!("llc failed with status: {}", status)); }

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
        if let Some(ref lvl) = args.opt { link_args.push(format!("-O{}", lvl)); }
        if args.debug { link_args.push("-g".to_string()); }
        link_args.extend(args.extra.clone());
        let mut cmd = Command::new(&clang);
        cmd.args(&link_args)
            .stdin(Stdio::null())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit());
        let status = run_with_timeout(cmd, timeout_from_env())
            .with_context(|| format!("failed to spawn {:?}", clang))?;
        if !status.success() { return Err(anyhow!("linking failed with status: {}", status)); }
        return Ok(());
    }

    // Optimization level for llc (for -S path as well)
    if let Some(ref lvl) = args.opt { llc_args.push(format!("-O{}", lvl)); }

    let mut cmd = Command::new(&llc);
    cmd.args(&llc_args)
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    let status = run_with_timeout(cmd, timeout_from_env())
        .with_context(|| format!("failed to spawn {:?}", llc))?;
    if !status.success() { return Err(anyhow!("llc failed with status: {}", status)); }

    Ok(())
}

fn cmd_run(args: &RunArgs) -> Result<()> {
    if !args.input.exists() {
        return Err(anyhow!("input file not found: {}", args.input.display()));
    }

    // Build to temp exe
    let pre = preprocess_capture(&args.input, &[])?;
    let tu = parse_translation_unit(&pre)?;
    check_translation_unit(&tu)?;
    let ir = emit_llvm_ir(&tu, "wyrmcc_module")?;

    let stem = args
        .input
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_else(|| "out".to_string());

    let dir = tempfile::tempdir()?;
    let ir_path = dir.path().join(format!("{}.ll", stem));
    fs::write(&ir_path, ir)?;

    let obj_path = dir.path().join(format!("{}.o", stem));

    let llc = resolve_llc_path()?;
    let mut llc_args: Vec<String> = vec![ir_path.display().to_string(), "-filetype=obj".to_string(), "-o".to_string(), obj_path.display().to_string()];
    if let Some(ref lvl) = args.opt { llc_args.push(format!("-O{}", lvl)); }

    let mut cmd = Command::new(&llc);
    cmd.args(&llc_args)
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    let status = run_with_timeout(cmd, timeout_from_env())
        .with_context(|| format!("failed to spawn {:?}", llc))?;
    if !status.success() { return Err(anyhow!("llc failed with status: {}", status)); }

    let exe_path = dir.path().join("a.out");
    let clang = resolve_clang_path()?;
    let mut link_args: Vec<String> = vec![
        "-no-pie".to_string(),
        obj_path.display().to_string(),
        "-o".to_string(),
        exe_path.display().to_string(),
    ];
    if let Some(ref lvl) = args.opt { link_args.push(format!("-O{}", lvl)); }
    if args.debug { link_args.push("-g".to_string()); }

    let mut cmd = Command::new(&clang);
    cmd.args(&link_args)
        .stdin(Stdio::null())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    let status = run_with_timeout(cmd, timeout_from_env())
        .with_context(|| format!("failed to spawn {:?}", clang))?;
    if !status.success() { return Err(anyhow!("linking failed with status: {}", status)); }

    // Run the program and propagate exit code
    let mut cmd = Command::new(&exe_path);
    cmd.args(&args.prog_args)
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    let status = run_with_timeout(cmd, timeout_from_env())
        .with_context(|| format!("failed to run {}", exe_path.display()))?;

    // Propagate exit code
    std::process::exit(status.code().unwrap_or(1));
}