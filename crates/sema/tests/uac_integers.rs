use parse::parse_translation_unit;
use sema::check_translation_unit;

// Usual arithmetic conversions: promotions of char/short to int
#[test]
fn promotions_char_short_to_int_ok() {
    let src = r#"
        int main(void) {
            char c = 1;
            short s = 2;
            int x = c + s; // both promote to int
            return x;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    assert!(res.is_ok(), "promotions (char/short -> int) in + should be accepted");
}

// Mixed signed/unsigned arithmetic should be accepted by sema
#[test]
fn mixed_signed_unsigned_add_ok() {
    let src = r#"
        int main(void) {
            int a = 1;
            unsigned int b = 2;
            int x = a + b; // usual arithmetic conversions apply
            (void)x;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    assert!(res.is_ok(), "int + unsigned int should be accepted");
}

// Shifts across signed/unsigned LHS should be accepted
#[test]
fn shifts_mixed_ok() {
    let src = r#"
        int main(void) {
            int x = 8;
            unsigned int u = 8;
            int a = x >> 1;
            int b = u >> 1; // unsigned logical shift in backend; sema should accept
            int c = x << 2;
            int d = u << 2;
            (void)a; (void)b; (void)c; (void)d;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    assert!(res.is_ok(), "mixed signed/unsigned shifts should be accepted");
}

// Comparisons under usual conversions (signed vs unsigned)
#[test]
fn comparisons_mixed_ok() {
    let src = r#"
        int main(void) {
            int a = -1;
            unsigned int b = 1;
            int r1 = (a < b);
            int r2 = (b > a);
            (void)r1; (void)r2;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    assert!(res.is_ok(), "mixed signed/unsigned comparisons should be accepted");
}