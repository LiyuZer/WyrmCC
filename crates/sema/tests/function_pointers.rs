use parse::parse_translation_unit;
use sema::check_translation_unit;

#[test]
fn sema_funcptr_decay_and_call_ok() {
    let src = r#"
        int f(int x) { return x + 1; }
        int main(void) {
            int (*p)(int) = f;   // function designator decays to pointer
            int (*r)(int) = &f;  // address-of function ok
            return p(3) + r(4);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(check_translation_unit(&tu).is_ok(), "expected sema ok for decay/address-of and call via pointer");
}

#[test]
fn sema_funcptr_assign_arity_mismatch_err() {
    let src = r#"
        int f(int);
        int (*q)(int, int) = f; // arity mismatch
        int main(void) { return 0; }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(check_translation_unit(&tu).is_err(), "expected sema error for assigning function to mismatched pointer arity");
}

#[test]
fn sema_funcptr_call_arg_type_mismatch_err() {
    let src = r#"
        int f(int);
        int (*t)(int) = f;
        int main(void) {
            // call via pointer with wrong argument type (pointer instead of int)
            return t((int*)0);
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(check_translation_unit(&tu).is_err(), "expected sema error for call via pointer with wrong arg type");
}

#[test]
fn sema_funcptr_call_too_few_args_err() {
    let src = r#"
        int g(int a, int b) { return a + b; }
        int main(void) {
            int (*p)(int,int) = g;
            return p(1); // too few args
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(check_translation_unit(&tu).is_err(), "expected sema error for too few args via function pointer");
}

#[test]
fn sema_funcptr_call_too_many_args_err() {
    let src = r#"
        int g(int a) { return a; }
        int main(void) {
            int (*p)(int) = g;
            return p(1, 2); // too many args
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(check_translation_unit(&tu).is_err(), "expected sema error for too many args via function pointer");
}

#[test]
fn sema_variadic_builtin_printf_assignment_ok() {
    let src = r#"
        int main(void) {
            // Assign builtin printf to a function pointer with fixed part (char*, ...) matching
            int (*vp)(char*, ...) = printf;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert!(check_translation_unit(&tu).is_ok(), "expected sema ok for assigning printf to variadic function pointer");
}
