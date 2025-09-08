use vstd::prelude::*;
use vstd::simple_pptr::*;
use verus_builtin_macros as builtin_macros;


verus! {

#[macro_export]
macro_rules! borrow_field {
    (& $ptr:expr) => {
        ::builtin_macros::verus_exec_expr!(
        $ptr
    )};
    (&mut $ptr:expr) => {
        ::builtin_macros::verus_exec_expr!(
        $ptr
    )};
    (& $ptr:expr => $field:tt, $perm:expr) => {
        ::builtin_macros::verus_exec_expr!(
        $ptr.borrow(Tracked($perm)).$field
    )};
    (&mut $ptr:expr => $field:tt, $perm:expr) => {
        ::builtin_macros::verus_exec_expr!(
        $ptr.borrow(Tracked($perm)).$field
    )}
}

#[macro_export]
macro_rules! update_field {
    ($ptr:expr => $field:tt <- $val:expr;
     $set:expr , $idx:expr) => {
        ::builtin_macros::verus_exec_expr!(
        {
            let tracked mut __own = $set.tracked_remove($idx);
            let mut __tmp = $ptr.take(Tracked(__own.self_perm.borrow_mut()));
            __tmp.$field = $val;
            $ptr.put(Tracked(__own.self_perm.borrow_mut()), __tmp);
            proof { $set.tracked_insert($idx, __own); }
        })
    };
    ($ptr:expr => $field:tt <- $val:expr;
     $set:expr , $idx:expr , $perm:tt) => {
        ::builtin_macros::verus_exec_expr!(
        {
            let tracked mut __own = $set.tracked_remove($idx);
            let mut __tmp = $ptr.take(Tracked(__own.$perm.borrow_mut()));
            __tmp.$field = $val;
            $ptr.put(Tracked(__own.$perm.borrow_mut()), __tmp);
            proof { $set.tracked_insert($idx, __own); }
        })
    };
    ($ptr:expr => $field:tt <- $val:expr;
     $perm:expr) => {
        ::builtin_macros::verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm.borrow_mut()));
            __tmp.$field = $val;
            $ptr.put(Tracked($perm.borrow_mut()), __tmp);
        })
    };
    ($ptr:expr => $field:tt += $val:expr;
     $perm:expr) => {
        ::builtin_macros::verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm.borrow_mut()));
            __tmp.$field = __tmp.$field + $val;
            $ptr.put(Tracked($perm.borrow_mut()), __tmp);
        })
    };
    ($ptr:expr => $field:tt -= $val:expr;
     $perm:expr) => {
        ::builtin_macros::verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm.borrow_mut()));
            __tmp.$field = __tmp.$field - $val;
            $ptr.put(Tracked($perm.borrow_mut()), __tmp);
        })
    }
}

}

pub use {
    borrow_field,
    update_field,
};