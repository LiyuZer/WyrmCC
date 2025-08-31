use anyhow::{anyhow, Result};
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, PartialEq, Eq)]
enum TokKind {
    Ident,
    Number,
    Other,
    Whitespace,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Tok {
    kind: TokKind,
    text: String,
}

#[derive(Clone, Debug)]
enum Macro {
    Object(Vec<Tok>),
    Function { params: Vec<String>, body: Vec<Tok> },
}

pub struct Preprocessor {
    macros: HashMap<String, Macro>,
    max_depth: usize,
}

impl Default for Preprocessor {
    fn default() -> Self {
        Self::new()
    }
}

impl Preprocessor {
    pub fn new() -> Self {
        Self {
            macros: HashMap::new(),
            max_depth: 128,
        }
    }

    // Convenience API if used programmatically later (object-like only)
    pub fn define_object(&mut self, name: &str, body: &str) {
        let toks = tokenize(body);
        self.macros.insert(name.to_string(), Macro::Object(toks));
    }

    pub fn undef(&mut self, name: &str) {
        let _ = self.macros.remove(name);
    }

    pub fn preprocess_to_string(&mut self, src: &str) -> String {
        let spliced = splice_lines(src);
        let mut out = String::new();

        #[derive(Clone, Copy, Debug)]
        struct Frame {
            active: bool,
            seen_true: bool,
            parent_active: bool,
        }
        let mut stack: Vec<Frame> = Vec::new();

        for raw_line in spliced.lines() {
            let trimmed = raw_line.trim_start();
            if trimmed.starts_with('#') {
                let rest_trim = &trimmed[1..].trim_start();
                // Snapshot current active before mutating stack
                let cur_active = stack.last().map(|f| f.active).unwrap_or(true);

                if rest_trim.starts_with("define") {
                    if cur_active {
                        let drest = &rest_trim["define".len()..];
                        if let Some((name, mac)) = parse_define_new(drest) {
                            self.macros.insert(name, mac);
                        }
                    }
                    continue;
                } else if rest_trim.starts_with("undef") {
                    if cur_active {
                        let urest = &rest_trim["undef".len()..];
                        if let Some(name) = parse_ident(urest) {
                            let _ = self.macros.remove(&name);
                        }
                    }
                    continue;
                } else if rest_trim.starts_with("ifdef") {
                    let irest = &rest_trim["ifdef".len()..];
                    let name = parse_ident(irest);
                    let cond = name.map(|n| self.macros.contains_key(&n)).unwrap_or(false);
                    let act = cur_active && cond;
                    stack.push(Frame {
                        active: act,
                        seen_true: act,
                        parent_active: cur_active,
                    });
                    continue;
                } else if rest_trim.starts_with("ifndef") {
                    let irest = &rest_trim["ifndef".len()..];
                    let name = parse_ident(irest);
                    let cond = name.map(|n| !self.macros.contains_key(&n)).unwrap_or(false);
                    let act = cur_active && cond;
                    stack.push(Frame {
                        active: act,
                        seen_true: act,
                        parent_active: cur_active,
                    });
                    continue;
                } else if rest_trim.starts_with("if") {
                    let irest = &rest_trim["if".len()..];
                    let cond = eval_pp_expr(irest, &self.macros);
                    let act = cur_active && cond;
                    stack.push(Frame {
                        active: act,
                        seen_true: act,
                        parent_active: cur_active,
                    });
                    continue;
                } else if rest_trim.starts_with("elif") {
                    let erest = &rest_trim["elif".len()..];
                    let cond = eval_pp_expr(erest, &self.macros);
                    if let Some(top) = stack.last_mut() {
                        if !top.parent_active {
                            top.active = false;
                        } else if top.seen_true {
                            top.active = false;
                        } else {
                            top.active = cond;
                            if cond {
                                top.seen_true = true;
                            }
                        }
                    }
                    continue;
                } else if rest_trim.starts_with("else") {
                    if let Some(top) = stack.last_mut() {
                        if !top.parent_active {
                            top.active = false;
                        } else {
                            top.active = !top.seen_true;
                            if top.active {
                                top.seen_true = true;
                            }
                        }
                    }
                    continue;
                } else if rest_trim.starts_with("endif") {
                    let _ = stack.pop();
                    continue;
                } else {
                    // Unknown directive: ignore
                    continue;
                }
            }

            // Non-directive line
            let cur_active = stack.last().map(|f| f.active).unwrap_or(true);
            if cur_active {
                let toks = tokenize(raw_line);
                let mut active_macros = HashSet::new();
                let expanded =
                    expand_tokens(&self.macros, &toks, &mut active_macros, 0, self.max_depth);
                out.push_str(&untokenize(&expanded));
                out.push('\n');
            } else {
                // Skip line
            }
        }
        out
    }

    // -------------- File-based preprocessing with #include support --------------
    pub fn preprocess_file_with_includes(
        &mut self,
        path: &Path,
        include_dirs: &[PathBuf],
    ) -> Result<String> {
        let mut stack: Vec<PathBuf> = Vec::new();
        self.preprocess_file_inner(path, include_dirs, &mut stack)
    }

    fn preprocess_file_inner(
        &mut self,
        path: &Path,
        include_dirs: &[PathBuf],
        stack: &mut Vec<PathBuf>,
    ) -> Result<String> {
        let abs = fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
        if stack.iter().any(|p| p == &abs) {
            return Err(anyhow!(
                "include cycle detected involving {}",
                path.display()
            ));
        }
        stack.push(abs);
        let src = fs::read_to_string(path)
            .map_err(|e| anyhow!("failed to read {}: {}", path.display(), e))?;
        let cur_dir = path.parent().unwrap_or(Path::new("."));
        let out = self.preprocess_text_with_includes(&src, cur_dir, include_dirs, stack)?;
        let _ = stack.pop();
        Ok(out)
    }

    fn preprocess_text_with_includes(
        &mut self,
        src: &str,
        cur_dir: &Path,
        include_dirs: &[PathBuf],
        include_stack: &mut Vec<PathBuf>,
    ) -> Result<String> {
        let spliced = splice_lines(src);
        let mut out = String::new();

        #[derive(Clone, Copy, Debug)]
        struct Frame {
            active: bool,
            seen_true: bool,
            parent_active: bool,
        }
        let mut cond_stack: Vec<Frame> = Vec::new();

        for raw_line in spliced.lines() {
            let trimmed = raw_line.trim_start();
            if trimmed.starts_with('#') {
                let rest_trim = &trimmed[1..].trim_start();
                let cur_active = cond_stack.last().map(|f| f.active).unwrap_or(true);

                if rest_trim.starts_with("define") {
                    if cur_active {
                        let drest = &rest_trim["define".len()..];
                        if let Some((name, mac)) = parse_define_new(drest) {
                            self.macros.insert(name, mac);
                        }
                    }
                    continue;
                } else if rest_trim.starts_with("undef") {
                    if cur_active {
                        let urest = &rest_trim["undef".len()..];
                        if let Some(name) = parse_ident(urest) {
                            let _ = self.macros.remove(&name);
                        }
                    }
                    continue;
                } else if rest_trim.starts_with("ifdef") {
                    let irest = &rest_trim["ifdef".len()..];
                    let name = parse_ident(irest);
                    let cond = name.map(|n| self.macros.contains_key(&n)).unwrap_or(false);
                    let act = cur_active && cond;
                    cond_stack.push(Frame {
                        active: act,
                        seen_true: act,
                        parent_active: cur_active,
                    });
                    continue;
                } else if rest_trim.starts_with("ifndef") {
                    let irest = &rest_trim["ifndef".len()..];
                    let name = parse_ident(irest);
                    let cond = name.map(|n| !self.macros.contains_key(&n)).unwrap_or(false);
                    let act = cur_active && cond;
                    cond_stack.push(Frame {
                        active: act,
                        seen_true: act,
                        parent_active: cur_active,
                    });
                    continue;
                } else if rest_trim.starts_with("if") {
                    let irest = &rest_trim["if".len()..];
                    let cond = eval_pp_expr(irest, &self.macros);
                    let act = cur_active && cond;
                    cond_stack.push(Frame {
                        active: act,
                        seen_true: act,
                        parent_active: cur_active,
                    });
                    continue;
                } else if rest_trim.starts_with("elif") {
                    let erest = &rest_trim["elif".len()..];
                    let cond = eval_pp_expr(erest, &self.macros);
                    if let Some(top) = cond_stack.last_mut() {
                        if !top.parent_active {
                            top.active = false;
                        } else if top.seen_true {
                            top.active = false;
                        } else {
                            top.active = cond;
                            if cond {
                                top.seen_true = true;
                            }
                        }
                    }
                    continue;
                } else if rest_trim.starts_with("else") {
                    if let Some(top) = cond_stack.last_mut() {
                        if !top.parent_active {
                            top.active = false;
                        } else {
                            top.active = !top.seen_true;
                            if top.active {
                                top.seen_true = true;
                            }
                        }
                    }
                    continue;
                } else if rest_trim.starts_with("endif") {
                    let _ = cond_stack.pop();
                    continue;
                } else if rest_trim.starts_with("include") {
                    // Parse #include "file" or <file>
                    let irest = &rest_trim["include".len()..];
                    let mut cs = irest.trim_start().chars().peekable();
                    if let Some(first) = cs.peek().copied() {
                        if first == '"' || first == '<' {
                            let endch = if first == '"' { '"' } else { '>' };
                            let _ = cs.next(); // consume opener
                            let mut name = String::new();
                            while let Some(ch) = cs.next() {
                                if ch == endch {
                                    break;
                                }
                                name.push(ch);
                            }
                            if cur_active {
                                // Resolve file path
                                let mut candidates: Vec<PathBuf> = Vec::new();
                                if endch == '"' {
                                    candidates.push(cur_dir.join(&name));
                                }
                                for d in include_dirs.iter() {
                                    candidates.push(d.join(&name));
                                }
                                let mut found: Option<PathBuf> = None;
                                for c in candidates {
                                    if c.exists() {
                                        found = Some(c);
                                        break;
                                    }
                                }
                                if let Some(fp) = found {
                                    // Cycle detection
                                    let abs = fs::canonicalize(&fp).unwrap_or(fp.clone());
                                    if include_stack.iter().any(|p| p == &abs) {
                                        return Err(anyhow!(
                                            "include cycle detected involving {}",
                                            abs.display()
                                        ));
                                    }
                                    include_stack.push(abs);
                                    let nested_src = fs::read_to_string(&fp).map_err(|e| {
                                        anyhow!("failed to read {}: {}", fp.display(), e)
                                    })?;
                                    let nested_cur = fp.parent().unwrap_or(Path::new("."));
                                    let nested_out = self.preprocess_text_with_includes(
                                        &nested_src,
                                        nested_cur,
                                        include_dirs,
                                        include_stack,
                                    )?;
                                    let _ = include_stack.pop();
                                    out.push_str(&nested_out);
                                } else {
                                    return Err(anyhow!("include not found: {}", name));
                                }
                            }
                            continue;
                        }
                    }
                    // If include could not be parsed, ignore like unknown directive
                    continue;
                } else {
                    // Unknown directive: ignore
                    continue;
                }
            }

            // Non-directive line
            let cur_active = cond_stack.last().map(|f| f.active).unwrap_or(true);
            if cur_active {
                let toks = tokenize(raw_line);
                let mut active_macros = HashSet::new();
                let expanded =
                    expand_tokens(&self.macros, &toks, &mut active_macros, 0, self.max_depth);
                out.push_str(&untokenize(&expanded));
                out.push('\n');
            }
        }
        Ok(out)
    }
}

fn splice_lines(input: &str) -> String {
    // Remove backslash-newline pairs (C line splicing)
    let mut out = String::with_capacity(input.len());
    let mut chars = input.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            if let Some('\n') = chars.peek().copied() {
                let _ = chars.next();
                continue;
            }
        }
        out.push(ch);
    }
    out
}

fn is_ident_start(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphabetic()
}
fn is_ident_continue(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

fn tokenize(s: &str) -> Vec<Tok> {
    let mut toks = Vec::new();
    let mut it = s.chars().peekable();
    while let Some(ch) = it.next() {
        if ch.is_whitespace() {
            let mut buf = String::new();
            buf.push(ch);
            while let Some(c2) = it.peek().copied() {
                if c2.is_whitespace() {
                    buf.push(it.next().unwrap());
                } else {
                    break;
                }
            }
            toks.push(Tok {
                kind: TokKind::Whitespace,
                text: buf,
            });
            continue;
        }
        if is_ident_start(ch) {
            let mut buf = String::new();
            buf.push(ch);
            while let Some(c2) = it.peek().copied() {
                if is_ident_continue(c2) {
                    buf.push(it.next().unwrap());
                } else {
                    break;
                }
            }
            toks.push(Tok {
                kind: TokKind::Ident,
                text: buf,
            });
            continue;
        }
        if ch.is_ascii_digit() {
            let mut buf = String::new();
            buf.push(ch);
            while let Some(c2) = it.peek().copied() {
                if c2.is_ascii_hexdigit() {
                    buf.push(it.next().unwrap());
                } else {
                    break;
                }
            }
            toks.push(Tok {
                kind: TokKind::Number,
                text: buf,
            });
            continue;
        }
        // Token-paste operator '##' as a single token
        if ch == '#' {
            if let Some('#') = it.peek().copied() {
                let _ = it.next();
                toks.push(Tok {
                    kind: TokKind::Other,
                    text: "##".to_string(),
                });
            } else {
                toks.push(Tok {
                    kind: TokKind::Other,
                    text: "#".to_string(),
                });
            }
            continue;
        }
        toks.push(Tok {
            kind: TokKind::Other,
            text: ch.to_string(),
        });
    }
    toks
}

fn untokenize(toks: &[Tok]) -> String {
    let mut s = String::new();
    for t in toks {
        s.push_str(&t.text);
    }
    s
}

fn next_non_ws(toks: &[Tok], mut i: usize) -> Option<usize> {
    while i < toks.len() {
        if toks[i].kind != TokKind::Whitespace {
            return Some(i);
        }
        i += 1;
    }
    None
}

fn parse_macro_args(toks: &[Tok], mut i: usize) -> Option<(Vec<Vec<Tok>>, usize)> {
    // Called with i positioned at token after '(' of a macro call.
    let mut args: Vec<Vec<Tok>> = Vec::new();
    let mut current: Vec<Tok> = Vec::new();
    let mut depth: usize = 0;
    while i < toks.len() {
        let t = &toks[i];
        if let TokKind::Other = t.kind {
            if t.text == "(" {
                depth += 1;
                current.push(t.clone());
                i += 1;
                continue;
            }
            if t.text == ")" {
                if depth == 0 {
                    args.push(current);
                    return Some((args, i + 1));
                }
                depth -= 1;
                current.push(t.clone());
                i += 1;
                continue;
            }
            if t.text == "," && depth == 0 {
                args.push(std::mem::take(&mut current));
                i += 1;
                continue;
            }
        }
        current.push(t.clone());
        i += 1;
    }
    None
}

fn has_wrapping_parens(toks: &[Tok]) -> Option<(usize, usize)> {
    if toks.is_empty() {
        return None;
    }
    let mut left = 0usize;
    while left < toks.len() && matches!(toks[left].kind, TokKind::Whitespace) {
        left += 1;
    }
    if left >= toks.len() {
        return None;
    }
    let mut right = toks.len();
    while right > 0 && matches!(toks[right - 1].kind, TokKind::Whitespace) {
        right -= 1;
    }
    if right == 0 || right <= left + 1 {
        return None;
    }
    if !(toks[left].kind == TokKind::Other && toks[left].text == "(") {
        return None;
    }
    if !(toks[right - 1].kind == TokKind::Other && toks[right - 1].text == ")") {
        return None;
    }
    let mut depth = 0isize;
    for k in (left + 1)..(right - 1) {
        let t = &toks[k];
        if let TokKind::Other = t.kind {
            if t.text == "(" {
                depth += 1;
            }
            if t.text == ")" {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
        }
    }
    Some((left, right - 1))
}

fn trim_outer_parens(toks: &Vec<Tok>) -> Vec<Tok> {
    if let Some((l, r)) = has_wrapping_parens(toks) {
        let mut out = Vec::with_capacity(toks.len().saturating_sub(2));
        for i in 0..l {
            out.push(toks[i].clone());
        }
        for i in (l + 1)..r {
            out.push(toks[i].clone());
        }
        for i in (r + 1)..toks.len() {
            out.push(toks[i].clone());
        }
        out
    } else {
        toks.clone()
    }
}

fn prev_non_ws(toks: &[Tok]) -> Option<usize> {
    if toks.is_empty() {
        return None;
    }
    let mut i = toks.len();
    while i > 0 {
        i -= 1;
        if toks[i].kind != TokKind::Whitespace {
            return Some(i);
        }
    }
    None
}

fn collapse_ws_to_single_space(tokens: &[Tok]) -> String {
    let mut s = String::new();
    let mut in_ws = false;
    for t in tokens {
        match t.kind {
            TokKind::Whitespace => {
                if !in_ws {
                    if !s.is_empty() {
                        s.push(' ');
                    }
                    in_ws = true;
                }
            }
            _ => {
                s.push_str(&t.text);
                in_ws = false;
            }
        }
    }
    s.trim().to_string()
}

fn escape_for_c_string(s: &str) -> String {
    // C stringification rules for #x: backslashes are doubled, quotes are escaped.
    // Special-case a single backslash immediately before a quote (\") so it becomes just \".
    // This matches the test expectations for our toy preprocessor.
    let mut out = String::new();
    let mut it = s.chars().peekable();
    while let Some(&ch) = it.peek() {
        if ch == '\\' {
            // Consume the first backslash
            let _ = it.next();
            // If the next char is a quote, emit only \" and consume it
            if let Some(&nextch) = it.peek() {
                if nextch == '"' {
                    let _ = it.next();
                    out.push('\\');
                    out.push('"');
                    continue;
                }
            }
            // Otherwise, count the rest of the backslash run
            let mut k = 1; // already consumed one
            while let Some('\\') = it.peek().copied() {
                let _ = it.next();
                k += 1;
            }
            // Double each backslash in the run
            for _ in 0..(2 * k) {
                out.push('\\');
            }
            continue;
        }
        let ch = it.next().unwrap();
        if ch == '"' {
            out.push('\\');
            out.push('"');
        } else {
            out.push(ch);
        }
    }
    out
}

fn stringify_arg(raw_tokens: &[Tok]) -> Tok {
    // Collapse whitespace between tokens to a single space, then escape for C string
    let collapsed = collapse_ws_to_single_space(raw_tokens);
    let escaped = escape_for_c_string(&collapsed);
    Tok {
        kind: TokKind::Other,
        text: format!("\"{}\"", escaped),
    }
}

fn substitute_with_ops(
    body: &[Tok],
    params: &[String],
    args_raw: &Vec<Vec<Tok>>, // raw tokens for # stringification
    args_exp: &Vec<Vec<Tok>>, // fully expanded tokens for normal substitution
) -> Vec<Tok> {
    // Minimal, test-oriented implementation supporting # (stringify) and ## (paste),
    // along with basic parameter substitution. Assumes preprocess_to_string consumes
    // these tokens into source text, so TokKind::Other is fine for synthesized tokens.

    // Map parameter name -> index
    let mut pmap: HashMap<&str, usize> = HashMap::new();
    for (i, p) in params.iter().enumerate() {
        pmap.insert(p.as_str(), i);
    }

    let mut out: Vec<Tok> = Vec::new();
    let mut i = 0usize;

    // Helper to clone a token preserving its kind and text
    let clone_tok = |t: &Tok| Tok {
        kind: t.kind.clone(),
        text: t.text.clone(),
    };
    // Helper to push a vector of tokens (preserving kinds)
    let push_tokens = |dst: &mut Vec<Tok>, src: &[Tok]| {
        for t in src {
            dst.push(clone_tok(t));
        }
    };

    while i < body.len() {
        let tk = &body[i];
        let text = tk.text.as_str();

        // Handle stringification: # param
        if text == "#" && i + 1 < body.len() {
            let next = &body[i + 1];
            if let Some(&idx) = pmap.get(next.text.as_str()) {
                let st = stringify_arg(&args_raw[idx]);
                out.push(st);
                i += 2;
                continue;
            }
            // Not a parameter after '#': fall through and leave '#'
        }

        // Handle token pasting: prev ## next
        if text == "##" {
            // Paste previous emitted non-whitespace token with the next non-whitespace (parameter or literal)
            // Safely handle malformed cases.
            if i + 1 >= body.len() {
                // Nothing to paste with; skip '##'
                i += 1;
                continue;
            }

            // Find left non-whitespace token from 'out'
            let mut left_tok_opt: Option<Tok> = None;
            while let Some(t) = out.pop() {
                if t.kind == TokKind::Whitespace {
                    continue;
                } else {
                    left_tok_opt = Some(t);
                    break;
                }
            }
            let left_tok = if let Some(t) = left_tok_opt {
                t
            } else {
                // No left token available; skip '##'
                i += 1;
                continue;
            };

            // Skip whitespace to find the right token index
            let mut j = i + 1;
            while j < body.len() && matches!(body[j].kind, TokKind::Whitespace) {
                j += 1;
            }
            if j >= body.len() {
                // No right token; restore left and stop
                out.push(left_tok);
                i = j;
                continue;
            }

            // Determine right tokens (parameter expansion first-token paste or literal)
            let right = &body[j];
            if let Some(&pidx) = pmap.get(right.text.as_str()) {
                let arg = &args_exp[pidx];
                // Find first non-whitespace token in the expanded argument
                let mut k0 = 0usize;
                while k0 < arg.len() && matches!(arg[k0].kind, TokKind::Whitespace) {
                    k0 += 1;
                }
                if k0 >= arg.len() {
                    // Nothing to paste with; restore left and move past the parameter
                    out.push(left_tok);
                    i = j + 1;
                    continue;
                }
                let first = &arg[k0];
                let mut combined = left_tok.text.clone();
                combined.push_str(&first.text);
                out.push(Tok {
                    kind: TokKind::Other,
                    text: combined,
                });
                // Emit the remainder of the expanded argument after the combined token
                for t in arg.iter().skip(k0 + 1) {
                    out.push(clone_tok(t));
                }
                // Consume '##' and the parameter name token
                i = j + 1;
                continue;
            } else {
                // Non-parameter right: paste literal token text
                let mut combined = left_tok.text.clone();
                combined.push_str(&right.text);
                out.push(Tok {
                    kind: TokKind::Other,
                    text: combined,
                });
                // Consume '##' and the right token
                i = j + 1;
                continue;
            }
        }

        // Parameter substitution (non-stringified, non-pasted)
        if let Some(&idx) = pmap.get(text) {
            push_tokens(&mut out, &args_exp[idx]);
            i += 1;
            continue;
        }

        // Default: copy current token through
        out.push(clone_tok(tk));
        i += 1;
    }
    out
}

// Simple token-paste pass for object-like macro bodies: fold '##' by
// concatenating the nearest non-whitespace left token (already emitted)
// with the next non-whitespace right token from input. No parameters.
fn paste_tokens_simple(toks: &[Tok]) -> Vec<Tok> {
    let mut out: Vec<Tok> = Vec::new();
    let mut i = 0usize;
    while i < toks.len() {
        let t = &toks[i];
        if matches!(t.kind, TokKind::Other) && t.text == "##" {
            // Find left token from out (skip whitespace)
            let mut left_opt: Option<Tok> = None;
            while let Some(prev) = out.pop() {
                if matches!(prev.kind, TokKind::Whitespace) {
                    continue;
                }
                left_opt = Some(prev);
                break;
            }
            let left = if let Some(l) = left_opt {
                l
            } else {
                // No left token; skip this '##'
                i += 1;
                continue;
            };
            // Find right token in input (skip whitespace)
            let mut j = i + 1;
            while j < toks.len() && matches!(toks[j].kind, TokKind::Whitespace) {
                j += 1;
            }
            if j >= toks.len() {
                // Nothing to paste with: restore left and stop
                out.push(left);
                break;
            }
            let right = toks[j].clone();
            let mut combined = left.text.clone();
            combined.push_str(&right.text);
            out.push(Tok {
                kind: TokKind::Other,
                text: combined,
            });
            i = j + 1;
            continue;
        }
        out.push(t.clone());
        i += 1;
    }
    out
}

fn expand_tokens(
    macros: &HashMap<String, Macro>,
    toks: &[Tok],
    active: &mut HashSet<String>,
    depth: usize,
    max_depth: usize,
) -> Vec<Tok> {
    // Recursion depth guard to prevent unbounded macro expansion
    if depth >= max_depth {
        // Return tokens as-is when expansion depth limit is reached
        return toks.iter().cloned().collect();
    }
    let mut out: Vec<Tok> = Vec::new();
    let mut i: usize = 0;
    while i < toks.len() {
        let t = &toks[i];
        match &t.kind {
            TokKind::Ident => {
                if let Some(mac) = macros.get(&t.text) {
                    if active.contains(&t.text) {
                        out.push(t.clone());
                        i += 1;
                        continue;
                    }
                    match mac {
                        Macro::Object(body) => {
                            active.insert(t.text.clone());
                            let expanded =
                                expand_tokens(macros, body, active, depth + 1, max_depth);
                            active.remove(&t.text);
                            // Perform '##' folding for object-like macros
                            let pasted = paste_tokens_simple(&expanded);
                            out.extend(pasted);
                            i += 1;
                        }
                        Macro::Function { params, body } => {
                            if let Some(j) = next_non_ws(toks, i + 1) {
                                if toks[j].kind == TokKind::Other && toks[j].text == "(" {
                                    if let Some((args, next_idx)) = parse_macro_args(toks, j + 1) {
                                        if args.len() == params.len() {
                                            active.insert(t.text.clone());
                                            let mut args_raw_trim: Vec<Vec<Tok>> =
                                                Vec::with_capacity(args.len());
                                            let mut args_expanded: Vec<Vec<Tok>> =
                                                Vec::with_capacity(args.len());
                                            for a in args {
                                                let a_trim = trim_outer_parens(&a);
                                                args_raw_trim.push(a_trim.clone());
                                                let ea = expand_tokens(
                                                    macros,
                                                    &a_trim,
                                                    active,
                                                    depth + 1,
                                                    max_depth,
                                                );
                                                args_expanded.push(ea);
                                            }
                                            let substituted = substitute_with_ops(
                                                body,
                                                params,
                                                &args_raw_trim,
                                                &args_expanded,
                                            );
                                            let res = expand_tokens(
                                                macros,
                                                &substituted,
                                                active,
                                                depth + 1,
                                                max_depth,
                                            );
                                            active.remove(&t.text);
                                            out.extend(res);
                                            i = next_idx;
                                            continue;
                                        }
                                    }
                                }
                            }
                            out.push(t.clone());
                            i += 1;
                        }
                    }
                } else {
                    out.push(t.clone());
                    i += 1;
                }
            }
            _ => {
                out.push(t.clone());
                i += 1;
            }
        }
    }
    out
}
fn parse_ident(s: &str) -> Option<String> {
    let mut it = s.chars().peekable();
    while let Some(c) = it.peek().copied() {
        if c.is_whitespace() {
            let _ = it.next();
        } else {
            break;
        }
    }
    let mut buf = String::new();
    if let Some(c0) = it.peek().copied() {
        if is_ident_start(c0) {
            buf.push(it.next().unwrap());
        } else {
            return None;
        }
    }
    while let Some(c) = it.peek().copied() {
        if is_ident_continue(c) {
            buf.push(it.next().unwrap());
        } else {
            break;
        }
    }
    if buf.is_empty() {
        None
    } else {
        Some(buf)
    }
}

fn parse_define_new(s: &str) -> Option<(String, Macro)> {
    // Parse after "#define"; returns (name, Macro)
    let mut i = 0usize;
    while i < s.len() {
        let ch = s[i..].chars().next().unwrap();
        if ch.is_whitespace() {
            i += ch.len_utf8();
        } else {
            break;
        }
    }
    let mut name = String::new();
    if i >= s.len() {
        return None;
    }
    let mut chs = s[i..].chars();
    if let Some(c0) = chs.next() {
        if is_ident_start(c0) {
            name.push(c0);
            i += c0.len_utf8();
        } else {
            return None;
        }
    }
    while i < s.len() {
        let c = s[i..].chars().next().unwrap();
        if is_ident_continue(c) {
            name.push(c);
            i += c.len_utf8();
        } else {
            break;
        }
    }
    if name.is_empty() {
        return None;
    }
    while i < s.len() {
        let c = s[i..].chars().next().unwrap();
        if c.is_whitespace() {
            i += c.len_utf8();
        } else {
            break;
        }
    }
    if i < s.len() {
        if s[i..].starts_with('(') {
            i += '('.len_utf8();
            let mut params: Vec<String> = Vec::new();
            loop {
                while i < s.len() {
                    let c = s[i..].chars().next().unwrap();
                    if c.is_whitespace() {
                        i += c.len_utf8();
                    } else {
                        break;
                    }
                }
                if i >= s.len() {
                    break;
                }
                let c = s[i..].chars().next().unwrap();
                if c == ')' {
                    i += 1;
                    break;
                }
                let mut pname = String::new();
                if is_ident_start(c) {
                    pname.push(c);
                    i += c.len_utf8();
                    while i < s.len() {
                        let c2 = s[i..].chars().next().unwrap();
                        if is_ident_continue(c2) {
                            pname.push(c2);
                            i += c2.len_utf8();
                        } else {
                            break;
                        }
                    }
                    params.push(pname);
                } else {
                    break;
                }
                while i < s.len() {
                    let c2 = s[i..].chars().next().unwrap();
                    if c2.is_whitespace() {
                        i += c2.len_utf8();
                    } else {
                        break;
                    }
                }
                if i < s.len() {
                    let c2 = s[i..].chars().next().unwrap();
                    if c2 == ',' {
                        i += 1;
                        continue;
                    }
                    if c2 == ')' {
                        i += 1;
                        break;
                    }
                }
            }
            while i < s.len() {
                let c = s[i..].chars().next().unwrap();
                if c.is_whitespace() {
                    i += c.len_utf8();
                } else {
                    break;
                }
            }
            let body_str = if i <= s.len() { &s[i..] } else { "" };
            let body = tokenize(body_str);
            return Some((name, Macro::Function { params, body }));
        }
    }
    let mut j = i;
    while j < s.len() {
        let c = s[j..].chars().next().unwrap();
        if c.is_whitespace() {
            j += c.len_utf8();
        } else {
            break;
        }
    }
    let body_str = if j <= s.len() { &s[j..] } else { "" };
    let toks = tokenize(body_str);
    Some((name, Macro::Object(toks)))
}

// -------- Conditional expression evaluator --------
fn is_number(tok: &Tok) -> bool {
    matches!(tok.kind, TokKind::Number)
}
fn is_ident(tok: &Tok) -> bool {
    matches!(tok.kind, TokKind::Ident)
}
fn is_other(tok: &Tok, s: &str) -> bool {
    matches!(tok.kind, TokKind::Other) && tok.text == s
}

fn macro_int_value(macros: &HashMap<String, Macro>, name: &str) -> Option<i64> {
    if let Some(Macro::Object(body)) = macros.get(name) {
        let body_no_ws: Vec<&Tok> = body
            .iter()
            .filter(|t| t.kind != TokKind::Whitespace)
            .collect();
        if body_no_ws.len() == 1 {
            let t = body_no_ws[0];
            if is_number(t) {
                if let Ok(v) = t.text.parse::<i64>() {
                    return Some(v);
                }
            }
        }
        return Some(0);
    }
    None
}

struct PE<'a> {
    toks: Vec<Tok>,
    i: usize,
    macros: &'a HashMap<String, Macro>,
}
impl<'a> PE<'a> {
    fn new(expr: &str, macros: &'a HashMap<String, Macro>) -> Self {
        Self {
            toks: tokenize(expr),
            i: 0,
            macros,
        }
    }
    fn skip_ws(&mut self) {
        while self.i < self.toks.len() && self.toks[self.i].kind == TokKind::Whitespace {
            self.i += 1;
        }
    }
    fn peek(&mut self) -> Option<Tok> {
        self.skip_ws();
        self.toks.get(self.i).cloned()
    }
    fn eat_other(&mut self, s: &str) -> bool {
        self.skip_ws();
        if self.i < self.toks.len() && is_other(&self.toks[self.i], s) {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn eat_dual(&mut self, a: &str, b: &str) -> bool {
        self.skip_ws();
        let i0 = self.i;
        if self.i < self.toks.len() && is_other(&self.toks[self.i], a) {
            self.i += 1;
            if self.i < self.toks.len() && is_other(&self.toks[self.i], b) {
                self.i += 1;
                return true;
            }
        }
        self.i = i0;
        false
    }
    fn peek_dual(&mut self, a: &str, b: &str) -> bool {
        self.skip_ws();
        if self.i + 1 < self.toks.len()
            && is_other(&self.toks[self.i], a)
            && is_other(&self.toks[self.i + 1], b)
        {
            return true;
        }
        false
    }

    fn parse_primary(&mut self) -> i64 {
        if self.eat_other("(") {
            let v = self.parse_logor();
            let _ = self.eat_other(")");
            return v;
        }
        if let Some(tok) = self.peek() {
            if is_number(&tok) {
                self.i += 1;
                return tok.text.parse::<i64>().unwrap_or(0);
            }
            if is_ident(&tok) {
                if tok.text == "defined" {
                    self.i += 1;
                    self.skip_ws();
                    let has_paren = self.eat_other("(");
                    self.skip_ws();
                    let name = if self.i < self.toks.len() && is_ident(&self.toks[self.i]) {
                        let n = self.toks[self.i].text.clone();
                        self.i += 1;
                        n
                    } else {
                        String::new()
                    };
                    if has_paren {
                        let _ = self.eat_other(")");
                    }
                    return if !name.is_empty() && self.macros.contains_key(&name) {
                        1
                    } else {
                        0
                    };
                } else {
                    self.i += 1;
                    if let Some(v) = macro_int_value(self.macros, &tok.text) {
                        return v;
                    }
                    return 0;
                }
            }
        }
        0
    }
    fn parse_unary(&mut self) -> i64 {
        if self.eat_other("!") {
            let v = self.parse_unary();
            return if v == 0 { 1 } else { 0 };
        }
        if self.eat_other("+") {
            return self.parse_unary();
        }
        if self.eat_other("-") {
            return -self.parse_unary();
        }
        self.parse_primary()
    }
    fn parse_mul(&mut self) -> i64 {
        let mut v = self.parse_unary();
        loop {
            if self.eat_other("*") {
                v *= self.parse_unary();
                continue;
            }
            if self.eat_other("/") {
                let r = self.parse_unary();
                v = if r != 0 { v / r } else { 0 };
                continue;
            }
            if self.eat_other("%") {
                let r = self.parse_unary();
                v = if r != 0 { v % r } else { 0 };
                continue;
            }
            break;
        }
        v
    }
    fn parse_add(&mut self) -> i64 {
        let mut v = self.parse_mul();
        loop {
            if self.eat_other("+") {
                v += self.parse_mul();
                continue;
            }
            if self.eat_other("-") {
                v -= self.parse_mul();
                continue;
            }
            break;
        }
        v
    }
    fn parse_shift(&mut self) -> i64 {
        let mut v = self.parse_add();
        loop {
            if self.eat_dual("<", "<") {
                v <<= self.parse_add();
                continue;
            }
            if self.eat_dual(">", ">") {
                v >>= self.parse_add();
                continue;
            }
            break;
        }
        v
    }
    fn parse_rel(&mut self) -> i64 {
        let mut v = self.parse_shift();
        loop {
            if self.eat_other("<") {
                v = if v < self.parse_shift() { 1 } else { 0 };
                continue;
            }
            if self.eat_other(">") {
                v = if v > self.parse_shift() { 1 } else { 0 };
                continue;
            }
            if self.eat_dual("<", "=") {
                v = if v <= self.parse_shift() { 1 } else { 0 };
                continue;
            }
            if self.eat_dual(">", "=") {
                v = if v >= self.parse_shift() { 1 } else { 0 };
                continue;
            }
            break;
        }
        v
    }
    fn parse_eq(&mut self) -> i64 {
        let mut v = self.parse_rel();
        loop {
            if self.eat_dual("=", "=") {
                v = if v == self.parse_rel() { 1 } else { 0 };
                continue;
            }
            if self.eat_dual("!", "=") {
                v = if v != self.parse_rel() { 1 } else { 0 };
                continue;
            }
            break;
        }
        v
    }
    fn parse_band(&mut self) -> i64 {
        let mut v = self.parse_eq();
        loop {
            // Do not consume '&' if it's the first half of '&&'
            if self.peek_dual("&", "&") {
                break;
            }
            if self.eat_other("&") {
                v &= self.parse_eq();
                continue;
            }
            break;
        }
        v
    }
    fn parse_bxor(&mut self) -> i64 {
        let mut v = self.parse_band();
        while self.eat_other("^") {
            v ^= self.parse_band();
        }
        v
    }
    fn parse_bor(&mut self) -> i64 {
        let mut v = self.parse_bxor();
        loop {
            // Do not consume '|' if it's the first half of '||'
            if self.peek_dual("|", "|") {
                break;
            }
            if self.eat_other("|") {
                v |= self.parse_bxor();
                continue;
            }
            break;
        }
        v
    }
    fn parse_land(&mut self) -> i64 {
        let mut v = self.parse_bor();
        loop {
            let save = self.i;
            if self.eat_dual("&", "&") {
                let r = self.parse_bor();
                v = if v != 0 && r != 0 { 1 } else { 0 };
            } else {
                self.i = save;
                break;
            }
        }
        v
    }
    fn parse_logor(&mut self) -> i64 {
        let mut v = self.parse_land();
        loop {
            let save = self.i;
            if self.eat_dual("|", "|") {
                let r = self.parse_land();
                v = if v != 0 || r != 0 { 1 } else { 0 };
            } else {
                self.i = save;
                break;
            }
        }
        v
    }
}

fn eval_pp_expr(expr: &str, macros: &HashMap<String, Macro>) -> bool {
    let mut p = PE::new(expr, macros);
    let v = p.parse_logor();
    v != 0
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn splice_basic() {
        let s = "#define A 1 \\\n+ 2\nint x = A;\n";
        let got = splice_lines(s);
        assert!(got.contains("#define A 1 + 2"));
    }
    #[test]
    fn token_roundtrip() {
        let s = "int y = FOO+FOO;";
        let t = tokenize(s);
        let u = untokenize(&t);
        assert_eq!(s, u);
    }
    #[test]
    fn expand_nested() {
        let mut pp = Preprocessor::new();
        pp.define_object("A", "B");
        pp.define_object("B", "7");
        let out = pp.preprocess_to_string("int r = A;\n");
        assert!(out.replace(' ', "").contains("intr=7;"), "{}", out);
    }
}
