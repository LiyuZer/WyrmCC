use sema::check_translation_unit;

#[test]
fn void_ptr_assignments_ok() {
    let src = r#"
        int main(void) {
            int x;
            int *ip = &x;
            void *vp;
            char *cp;
            vp = ip;   // T* -> void*
            ip = vp;   // void* -> T*
            cp = vp;   // void* -> char*
            vp = cp;   // char* -> void*
            return 0;
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("sema ok: void* conversions in assignments");
}

#[test]
fn void_ptr_params_and_null_ok() {
    let src = r#"
        int f(void *p) { return 0; }
        int h(char *p) { return 0; }
        int main(void) {
            int x;
            int *ip = &x;
            void *vp = 0;
            f(ip);       // T* -> void* param
            f(0);        // null pointer constant to void* param
            h(vp);       // void* -> char* param (implicit)
            return 0;
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("sema ok: void* conversions in params and null constant");
}

#[test]
fn pointer_equals_null_ok() {
    let src = r#"
        int main(void) {
            int *p = 0;
            return p == 0; // equality with null pointer constant
        }
    "#;
    let tu = parse::parse_translation_unit(src).expect("parse ok");
    check_translation_unit(&tu).expect("sema ok: pointer equality with 0");
}
