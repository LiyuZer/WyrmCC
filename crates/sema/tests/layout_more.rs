use parse::parse_translation_unit;
use sema::build_record_layouts;

// Verify struct layout with mixed int and pointer members on x86_64-like target
// Expected: a:off=0 (i32), p:off=8 (ptr, aligned to 8), b:off=16 (i32); size=24, align=8
#[test]
fn struct_mixed_int_ptr_layout() {
    let src = r#"
        int main(void) {
            struct Mix { int a; int *p; int b; } m;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let (smap, _umap) = build_record_layouts(&tu);
    let s = smap.get("").or_else(|| smap.get("Mix")).expect("struct layout present");

    let (off_a, _ty_a) = s.members.get("a").expect("field a");
    let (off_p, _ty_p) = s.members.get("p").expect("field p");
    let (off_b, _ty_b) = s.members.get("b").expect("field b");

    assert_eq!(*off_a, 0, "a offset");
    assert_eq!(*off_p, 8, "p offset (8-byte aligned)");
    assert_eq!(*off_b, 16, "b offset");
    assert_eq!(s.size, 24, "struct size rounded up to max align");
    assert_eq!(s.align, 8, "struct align is max member align");
}

// Verify union layout size/align use max of members
#[test]
fn union_int_and_ptr_layout() {
    let src = r#"
        int main(void) {
            union U { int i; int *p; } u;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let (_smap, umap) = build_record_layouts(&tu);
    let u = umap.get("").or_else(|| umap.get("U")).expect("union layout present");

    assert_eq!(u.size, 8, "union size = max( sizeof(int)=4, sizeof(ptr)=8 )");
    assert_eq!(u.align, 8, "union align = max(member align) = 8");
    assert!(u.members.get("i").is_some());
    assert!(u.members.get("p").is_some());
}

// Struct with int then pointer: expect pointer aligned up to 8 and size rounded to 16.
#[test]
fn struct_int_then_ptr_layout_s() {
    let src = r#"
        int main(void) {
            struct S { int a; int *p; } s;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let (smap, _umap) = build_record_layouts(&tu);
    let s = smap.get("").or_else(|| smap.get("S")).expect("struct S layout");

    let (off_a, _ty_a) = s.members.get("a").expect("field a");
    let (off_p, _ty_p) = s.members.get("p").expect("field p");

    assert_eq!(*off_a, 0, "a@0");
    assert_eq!(*off_p, 8, "p@8 aligned to 8");
    assert_eq!(s.align, 8, "align(S)=8");
    assert_eq!(s.size, 16, "sizeof(S)=16");
}

// Struct with pointer then int: int should be at offset 8; size 16, align 8.
#[test]
fn struct_ptr_then_int_layout_t() {
    let src = r#"
        int main(void) {
            struct T { int *p; int a; } t;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let (smap, _umap) = build_record_layouts(&tu);
    let s = smap.get("").or_else(|| smap.get("T")).expect("struct T layout");

    let (off_p, _ty_p) = s.members.get("p").expect("field p");
    let (off_a, _ty_a) = s.members.get("a").expect("field a");

    assert_eq!(*off_p, 0, "p@0");
    assert_eq!(*off_a, 8, "a@8 after 8-byte pointer");
    assert_eq!(s.align, 8, "align(T)=8");
    assert_eq!(s.size, 16, "sizeof(T)=16");
}

// Nested struct alignment propagation: inner struct placed after an i32; pointer must align to 8.
#[test]
fn nested_struct_alignment_propagation_o() {
    let src = r#"
        int main(void) {
            struct I { int a; };
            struct O { int x; struct I i; int *q; } o;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let (smap, _umap) = build_record_layouts(&tu);

    // Check inner struct I layout assumptions
    let i_l = smap.get("I").expect("struct I layout");
    assert_eq!(i_l.size, 4, "sizeof(I)=4");
    assert_eq!(i_l.align, 4, "align(I)=4");
    let (off_a, _ty_a) = i_l.members.get("a").expect("I.a");
    assert_eq!(*off_a, 0, "I.a@0");

    let o = smap.get("").or_else(|| smap.get("O")).expect("struct O layout");
    let (off_x, _ty_x) = o.members.get("x").expect("field x");
    let (off_i, _ty_i) = o.members.get("i").expect("field i");
    let (off_q, _ty_q) = o.members.get("q").expect("field q");

    assert_eq!(*off_x, 0, "x@0");
    assert_eq!(*off_i, 4, "i placed after x with 4-byte align");
    assert_eq!(*off_q, 8, "q aligned up to 8 after i");
    assert_eq!(o.align, 8, "align(O)=8 (due to pointer)");
    assert_eq!(o.size, 16, "sizeof(O)=16");
}

// Simple struct of two ints: size 8, align 4. Useful for arrays-of-structs expectations elsewhere.
#[test]
fn struct_two_ints_size_align_p() {
    let src = r#"
        int main(void) {
            struct P { int x; int y; } p;
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let (smap, _umap) = build_record_layouts(&tu);
    let p = smap.get("").or_else(|| smap.get("P")).expect("struct P layout");

    let (off_x, _ty_x) = p.members.get("x").expect("x");
    let (off_y, _ty_y) = p.members.get("y").expect("y");

    assert_eq!(*off_x, 0, "x@0");
    assert_eq!(*off_y, 4, "y@4");
    assert_eq!(p.size, 8, "sizeof(P)=8");
    assert_eq!(p.align, 4, "align(P)=4");
}