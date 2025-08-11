#[macro_export]
macro_rules! borrow_field {
    (& mut $ptr:expr) => {
        &mut $ptr
    };
    (& $ptr:expr => $field:tt, NonNull) => {
        (unsafe { $ptr.as_ref() }).$field
    };
    (& mut $ptr:expr => $field:tt, NonNull) => {
        (unsafe { $ptr.as_mut() }).$field
    };
    (& mut $ref:expr => $field:tt) => {
        &mut $ref.$field
    };
}

#[macro_export]
macro_rules! update_field {
    ($ptr:expr => $field:tt <- $val:expr, NonNull) => {
        let __ptr = unsafe { $ptr.as_mut() };
        __ptr.$field = $val;
    };
    ($ptr:expr => $field:tt <- $val:expr) => {
        $ptr.$field = $val;
    };
    ($ptr:expr => $field:tt += $val:expr) => {
        $ptr.$field = $ptr.$field + $val;
    };
    ($ptr:expr => $field:tt -= $val:expr) => {
        $ptr.$field = $ptr.$field - $val;
    }
}