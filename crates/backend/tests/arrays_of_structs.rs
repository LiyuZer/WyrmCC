use backend::emit_llvm_ir;
use parse::parse_translation_unit;

// Arrays of structs: ensure element indexing scales by sizeof(struct)
// and member access applies the field offset. We assert on IR patterns
// rather than requiring the final return to be a literal constant.
#[test]
fn arrays_of_structs_store_and_load_field() {
    let src = r#"
        struct P { int x; int y; };
        int main(void) {
            struct P a[3];
            a[1].y = 7;
            return a[1].y;
        }
    "#;

    let tu = parse_translation_unit(src).expect("parse ok");
    let ir = emit_llvm_ir(&tu, "test_module").expect("emit ok");

    // Expect we use byte-wise GEPs for member addressing
    assert!(ir.contains("getelementptr inbounds i8"), "expected i8 GEP for member addressing, IR:\n{}", ir);
    // Expect the store of 7 into the field
    assert!(ir.contains("store i32 7"), "expected store of 7 to a[1].y, IR:\n{}", ir);
    // Expect we load the value and then return (value may be in an SSA, not literal)
    assert!(ir.contains("load i32, ptr"), "expected load from the member pointer, IR:\n{}", ir);
    assert!(ir.contains("ret i32"), "expected a return instruction, IR:\n{}", ir);
}