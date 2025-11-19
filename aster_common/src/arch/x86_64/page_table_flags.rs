use vstd::prelude::*;

verus! {

pub struct PageTableFlags {}

#[allow(non_snake_case)]
impl PageTableFlags {
    /// Specifies whether the mapped frame or page table is loaded in memory.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn PRESENT() -> (res: usize)
        ensures
            res == Self::PRESENT_spec(),
    {
        0b00000001usize
    }

    /// Controls whether writes to the mapped frames are allowed.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn WRITABLE() -> (res: usize)
        ensures
            res == Self::WRITABLE_spec(),
    {
        0b00000010usize
    }

    /// Controls whether accesses from userspace (i.e. ring 3) are permitted.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn USER() -> (res: usize)
        ensures
            res == Self::USER_spec(),
    {
        0b00000100usize
    }

    /// If this bit is set, a “write-through” policy is used for the cache, else a “write-back” policy is used.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn WRITE_THROUGH() -> (res: usize)
        ensures
            res == Self::WRITE_THROUGH_spec(),
    {
        0b00001000usize
    }

    /// Disables caching for the pointed entry if cacheable.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn NO_CACHE() -> (res: usize)
        ensures
            res == Self::NO_CACHE_spec(),
    {
        0b00010000usize
    }

    /// Whether this entry has been used for linear-address translation.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn ACCESSED() -> (res: usize)
        ensures
            res == Self::ACCESSED_spec(),
    {
        0b00100000usize
    }

    /// Whether the memory area represented by this entry is modified.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn DIRTY() -> (res: usize)
        ensures
            res == Self::DIRTY_spec(),
    {
        0b01000000usize
    }

    /// Only in the non-starting and non-ending levels, indication of huge page.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn HUGE() -> (res: usize)
        ensures
            res == Self::HUGE_spec(),
    {
        0b10000000usize
    }

    /// Indicates that the mapping is present in all address spaces, so it isn't flushed from the TLB on an address space switch.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn GLOBAL() -> (res: usize)
        ensures
            res == Self::GLOBAL_spec(),
    {
        0b00000001_00000000usize
    }

    /// Forbid constute codes on the page. The NXE bits in EFER msr must be set.
    #[inline(always)]
    #[vstd::contrib::auto_spec]
    pub const fn NO_EXECUTE() -> (res: usize)
        ensures
            res == Self::NO_EXECUTE_spec(),
    {
        1usize << 63
    }
}

} // verus!
