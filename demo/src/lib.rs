#![no_std]

use core::cell::UnsafeCell;

pub struct DataCell<'a> {
    data: &'a mut usize,
}

impl DataCell<'_> {
    pub fn set(self, data: usize) {
        *self.data = data;
    }

    pub fn as_ptr(self) -> *const usize {
        self.data as *const usize
    }
}