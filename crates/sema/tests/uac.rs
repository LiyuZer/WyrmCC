use parse::ast::Type;
use sema::{promoted_int_type, arith_result_type, shift_result_lhs_promoted, cond_result_type};

fn t(ty: Type) -> Type { ty }

#[test]
fn promotions_basic() {
    // Narrow types promote to int on this target
    assert!(matches!(promoted_int_type(&Type::Char),   Some(Type::Int)));
    assert!(matches!(promoted_int_type(&Type::SChar),  Some(Type::Int)));
    assert!(matches!(promoted_int_type(&Type::UChar),  Some(Type::Int)));
    assert!(matches!(promoted_int_type(&Type::Short),  Some(Type::Int)));
    assert!(matches!(promoted_int_type(&Type::UShort), Some(Type::Int)));

    // 32-bit types stay the same
    assert!(matches!(promoted_int_type(&Type::Int),   Some(Type::Int)));
    assert!(matches!(promoted_int_type(&Type::UInt),  Some(Type::UInt)));
    assert!(matches!(promoted_int_type(&Type::Long),  Some(Type::Long)));
    assert!(matches!(promoted_int_type(&Type::ULong), Some(Type::ULong)));
}

#[test]
fn uac_key_combinations() {
    // After promotions: (int, int) => int
    assert!(matches!(arith_result_type(&t(Type::Short), &t(Type::Short)), Some(Type::Int)));

    // int vs uint => uint
    assert!(matches!(arith_result_type(&t(Type::Int), &t(Type::UInt)), Some(Type::UInt)));
    assert!(matches!(arith_result_type(&t(Type::Short), &t(Type::UInt)), Some(Type::UInt)));

    // long vs int => long
    assert!(matches!(arith_result_type(&t(Type::Long), &t(Type::Int)), Some(Type::Long)));
    assert!(matches!(arith_result_type(&t(Type::Int), &t(Type::Long)), Some(Type::Long)));

    // long vs uint (both 32-bit ranks here) => unsigned long
    assert!(matches!(arith_result_type(&t(Type::Long), &t(Type::UInt)), Some(Type::ULong)));
    assert!(matches!(arith_result_type(&t(Type::UInt), &t(Type::Long)), Some(Type::ULong)));

    // any with unsigned long => unsigned long
    assert!(matches!(arith_result_type(&t(Type::ULong), &t(Type::Int)),  Some(Type::ULong)));
    assert!(matches!(arith_result_type(&t(Type::ULong), &t(Type::UInt)), Some(Type::ULong)));
    assert!(matches!(arith_result_type(&t(Type::Long),  &t(Type::ULong)), Some(Type::ULong)));
}

#[test]
fn shift_result_is_promoted_lhs() {
    // short << int => result type is promoted(short) = int
    assert!(matches!(shift_result_lhs_promoted(&Type::Short),  Some(Type::Int)));
    assert!(matches!(shift_result_lhs_promoted(&Type::UShort), Some(Type::Int)));

    // int << anything => int
    assert!(matches!(shift_result_lhs_promoted(&Type::Int), Some(Type::Int)));

    // long << anything => long
    assert!(matches!(shift_result_lhs_promoted(&Type::Long), Some(Type::Long)));
}

#[test]
fn cond_operator_uses_uac_for_ints() {
    // short : uint -> promotions then uac => uint
    assert!(matches!(cond_result_type(&t(Type::Short), &t(Type::UInt)), Some(Type::UInt)));

    // long : int => long
    assert!(matches!(cond_result_type(&t(Type::Long), &t(Type::Int)), Some(Type::Long)));

    // ulong : int => ulong
    assert!(matches!(cond_result_type(&t(Type::ULong), &t(Type::Int)), Some(Type::ULong)));

    // char : unsigned char => both promote to int => int
    assert!(matches!(cond_result_type(&t(Type::Char), &t(Type::UChar)), Some(Type::Int)));
}
