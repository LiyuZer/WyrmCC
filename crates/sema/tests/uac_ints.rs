use parse::parse_translation_unit;
use sema::check_translation_unit;

#[test]
fn promotions_and_mixed_arith_ok() {
    let src = r#"
        int f(void) {
            char c = 1;
            signed char sc = -2;
            unsigned char uc = 3;
            short s = 2;
            unsigned short us = 5;
            int x = 0;
            x = c + s;
            x = c * s;
            x = c / s;
            x = c % s;
            x = c << 1;
            x = s >> 1;
            x = sc + us;
            x = uc + us;
            x = uc - sc;
            return x;
        }

        int g(void) {
            int a = -1;
            unsigned int b = 1;
            int r1 = a < b;
            int r2 = a <= b;
            int r3 = a > b;
            int r4 = a >= b;
            int r5 = (a == b);
            int r6 = (a != b);
            int r7 = a + b;
            int r8 = a - b;
            int r9 = a * b;
            int r10 = a / b;
            int r11 = a % b;
            int r12 = a >> 1;
            unsigned int r13 = b >> 1;
            return r1+r2+r3+r4+r5+r6+r7+r8+r9+r10+r11+r12+r13;
        }

        int h(int a, unsigned b) {
            int t = (a ? a : b);
            int u = (b ? b : a);
            return t + u;
        }
    "#;

    let tu = parse_translation_unit(src).expect("parse ok");
    let res = check_translation_unit(&tu);
    assert!(res.is_ok(), "expected UAC-related mixes to type-check without diagnostics, got: {:?}", res.err());
}