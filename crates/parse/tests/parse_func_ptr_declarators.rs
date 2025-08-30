use parse::{ast::*, parse_translation_unit};

fn expect_fnptr_ty(ty: &Type, param_count: usize, variadic: bool) {
    match ty {
        Type::Pointer(inner) => match &**inner {
            Type::Func { ret, params, variadic: v } => {
                assert!(matches!(**ret, Type::Int), "return type should be int, got {:?}", ret);
                assert_eq!(params.len(), param_count, "param count mismatch: {:?}", params);
                assert_eq!(*v, variadic, "variadic flag mismatch");
                for p in params { assert!(matches!(p, Type::Int), "param type should be int, got {:?}", p); }
            }
            other => panic!("expected pointer to function type, got {:?}", other),
        },
        other => panic!("expected pointer type, got {:?}", other),
    }
}

#[test]
fn global_function_pointer_declarator_parses() {
    // int (*fp)(int, int);
    let src = r#"
        int (*fp)(int, int);
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    assert_eq!(tu.globals.len(), 1, "expected one global");
    let g = &tu.globals[0];
    assert_eq!(g.name, "fp");
    expect_fnptr_ty(&g.ty, 2, false);
}

#[test]
fn typedef_function_pointer_parses_inside_function() {
    // int main(void){ typedef int (*FN)(int,int); return 0; }
    let src = r#"
        int main(void){
            typedef int (*FN)(int,int);
            return 0;
        }
    "#;
    let tu = parse_translation_unit(src).expect("parse ok");
    let f = tu.functions.iter().find(|f| f.name == "main").expect("main present");
    // Find the typedef statement
    let mut found = false;
    for s in &f.body {
        if let Stmt::Typedef { name, ty } = s {
            if name == "FN" {
                expect_fnptr_ty(ty, 2, false);
                found = true;
            }
        }
    }
    assert!(found, "expected typedef FN inside main body");
}
