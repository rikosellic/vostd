use vstd::prelude::*;
use vstd::simple_pptr::*;

verus! {

#[macro_export]
macro_rules! update_field {
    ($ptr:expr => $field:tt <- $val:expr,
     $perm:expr) => {
        ::builtin_macros::verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm));
            __tmp.$field = $val;
            $ptr.put(Tracked($perm), __tmp);
        })
    };
    ($ptr:expr => $field:tt += $val:expr,
     $perm:expr) => {
        ::builtin_macros::verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm));
            __tmp.$field = __tmp.$field + $val;
            $ptr.put(Tracked($perm), __tmp);
        })
    };
    ($ptr:expr => $field:tt -= $val:expr,
     $perm:expr) => {
        ::builtin_macros::verus_exec_expr!(
        {
            let mut __tmp = $ptr.take(Tracked($perm));
            __tmp.$field = __tmp.$field - $val;
            $ptr.put(Tracked($perm), __tmp);
        })
    }
}

}