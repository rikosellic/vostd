use vstd::prelude::*;
use core::num;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Mutex, OnceLock};

use crate::mm::entry::Entry;
use crate::mm::page_prop::{PageFlags, PageProperty, PrivilegedPageFlags};
use crate::mm::page_table::PageTableNode;

use crate::mm::{pte_index, Paddr, NR_ENTRIES};
use crate::{
    mm::{
        cursor::{Cursor, CursorMut},
        meta::{AnyFrameMeta, MetaSlot},
        page_prop, Frame, PageTableEntryTrait, PageTableLockTrait, PageTablePageMeta, PagingConsts,
        PagingConstsTrait, UserMode, Vaddr, MAX_USERSPACE_VADDR, NR_LEVELS, PAGE_SIZE,
    },
    spec::simple_page_table,
    task::{disable_preempt, DisabledPreemptGuard},
};
use vstd::simple_pptr::*;

use crate::exec;

verus! {

pub const SIZEOF_PAGETABLEENTRY: usize = 24;
global layout SimplePageTableEntry is size == 24, align == 8;

pub const SIZEOF_FRAME: usize = 24 * 512; // 8 bytes for pa + 8 bytes for each pte
global layout SimpleFrame is size == 12288, align == 8;

pub const MAX_FRAME_NUM: usize = 10000;

// TODO: This is a mock implementation of the page table entry.
// Maybe it should be replaced with the actual implementation, e.g., x86_64.
#[derive(Copy, Clone)]
pub struct SimplePageTableEntry {
    pub pte_addr: u64,
    pub frame_pa: u64,
    pub level: u8,
    // pub prop: PageProperty,
}

#[derive(Copy, Clone)]
pub struct SimpleFrame {
    // TODO: Is this correct?
    pub ptes: [SimplePageTableEntry; NR_ENTRIES],
    // pub ptes: Vec<SimplePageTableEntry>,
}

impl PageTableEntryTrait for SimplePageTableEntry {

    fn is_present(&self, mpt: &MockPageTable) -> bool {
        assert(self.frame_pa != 0 ==>
                mpt.ptes@.value().contains_key(self.pte_addr as int));
        assert(self.frame_pa != 0 ==>
                mpt.frames@.value().contains_key(self.frame_pa as int)) by { admit(); } // TODO: P0
        assert(self.frame_pa == 0 ==>
                    !mpt.ptes@.value().contains_key(self.pte_addr as int)) by { admit(); } // TODO: P0
        self.frame_pa != 0
    }

    fn frame_paddr(&self) -> (res: usize)
    ensures
        res == self.frame_paddr_spec()
    {
        self.frame_pa as usize
    }

    open spec fn frame_paddr_spec(&self) -> Paddr {
        self.frame_pa as Paddr
    }

    #[verifier::external_body]
    fn is_last(&self, level: u8) -> bool {
        unimplemented!()
    }

    #[verifier::external_body]
    fn new_page(paddr: crate::mm::Paddr, level: crate::mm::PagingLevel, prop: crate::mm::page_prop::PageProperty, mpt: &mut MockPageTable) -> Self {
        SimplePageTableEntry {
            pte_addr: 0,
            frame_pa: 0,
            level: 0, // level 0 represent a page
        }
    }

    #[verifier::external_body]
    fn new_pt(paddr: crate::mm::Paddr) -> Self {
        SimplePageTableEntry {
            pte_addr: 0, // invalid
            frame_pa: paddr as u64,
            level: 0, // invalid
        }
    }

    #[verifier::external_body]
    fn new_token(token: crate::mm::vm_space::Token) -> Self {
        todo!()
    }

    #[verifier::external_body]
    fn prop(&self) -> crate::mm::page_prop::PageProperty {
        todo!()
    }

    #[verifier::external_body]
    fn set_prop(&mut self, prop: crate::mm::page_prop::PageProperty) {
        todo!()
    }

    #[verifier::external_body]
    fn set_paddr(&mut self, paddr: crate::mm::Paddr) {
        todo!()
    }

    #[verifier::external_body]
    fn new_absent() -> Self {
        // Self::default()
        std::unimplemented!()
    }

    #[verifier::external_body]
    fn as_usize(self) -> usize {
        // SAFETY: `Self` is `Pod` and has the same memory representation as `usize`.
        // unsafe { transmute_unchecked(self) }
        // TODO: Implement this function
        std::unimplemented!()
    }

    fn from_usize(pte_raw: usize, mpt: &MockPageTable) -> (res: Self)
    ensures
        res == get_pte_from_addr_spec(pte_raw, mpt)
    {
        assert(0 <= pte_raw < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_PAGETABLEENTRY * NR_ENTRIES) by { admit(); } // TODO
        assert((pte_raw - PHYSICAL_BASE_ADDRESS_SPEC()) % SIZEOF_PAGETABLEENTRY as int == 0) by { admit(); } // TODO
        get_pte_from_addr(pte_raw, mpt)
    }

    fn pte_paddr(&self) -> (res: Paddr)
    ensures res == self.pte_addr_spec() {
        self.pte_addr as Paddr
    }

    open spec fn pte_addr_spec(&self) -> Paddr {
        self.pte_addr as Paddr
    }
}

pub struct SimpleFrameMeta {}

impl AnyFrameMeta for SimpleFrameMeta {
}

// TODO: This FakePageTableLock will ignore Entry and MetaSlot.
// TODO: We possibly need to use PageTableNode later.
pub struct FakePageTableLock<E: PageTableEntryTrait, C: PagingConstsTrait> {
    pub paddr: Paddr,
    pub phantom: std::marker::PhantomData<(E, C)>,
}

impl<E: PageTableEntryTrait, C: PagingConstsTrait> PageTableLockTrait<E, C> for FakePageTableLock<E, C> {

    // #[verifier::external_body]
    // fn entry(&self, idx: usize) -> crate::mm::entry::Entry<'_, E, C, Self> {
    //     Entry::new_at(self, idx)
    // }

    fn paddr(&self) -> crate::mm::Paddr {
        self.paddr
    }

    fn alloc(level: crate::mm::PagingLevel, is_tracked: crate::mm::MapTrackingStatus,
            // ghost
            mpt: &mut exec::MockPageTable,
            instance: Tracked<simple_page_table::SimplePageTable::Instance>,
            cur_alloc_index: usize,
            used_addr: usize,
            used_addr_token: Tracked<simple_page_table::SimplePageTable::unused_addrs>,
    ) -> (res: Self) where Self: Sized {

        broadcast use vstd::std_specs::hash::group_hash_axioms;
        broadcast use vstd::hash_map::group_hash_map_axioms;
        // print_num(cur_alloc_index);
        let (p, Tracked(pt)) = get_frame_from_index(cur_alloc_index, &mpt.mem); // TODO: permission violation
        p.write(Tracked(&mut pt), SimpleFrame {
            ptes: {
                let mut ptes = [SimplePageTableEntry {
                    pte_addr: 0,
                    frame_pa: 0,
                    level: 0,
                }; NR_ENTRIES];
                for i in 0..NR_ENTRIES {
                    assert((PHYSICAL_BASE_ADDRESS() as u64 + cur_alloc_index as u64 * SIZEOF_FRAME as u64 + i as u64 * SIZEOF_PAGETABLEENTRY as u64) < usize::MAX as u64) by { admit(); }; // TODO
                    ptes[i] = SimplePageTableEntry {
                        pte_addr: PHYSICAL_BASE_ADDRESS() as u64 + cur_alloc_index as u64 * SIZEOF_FRAME as u64 + i as u64 * SIZEOF_PAGETABLEENTRY as u64,
                        frame_pa: 0,
                        level: level as u8,
                    };
                }
                ptes
            },
        });

        assert(p.addr() == used_addr);

        mpt.mem.remove(&cur_alloc_index);
        assert(mpt.mem.len() == MAX_FRAME_NUM - 1); // NOTE: need to be finite
        mpt.mem.insert(cur_alloc_index, (p, Tracked(pt)));
        assert(mpt.mem.len() == MAX_FRAME_NUM);
        assert(mpt.mem@.contains_key(cur_alloc_index));

        proof {
            assert(forall |i: int| 0 <= i < NR_ENTRIES ==>
                    ! (#[trigger] mpt.ptes@.value().dom().contains(p.addr() + i * simple_page_table::SIZEOF_PAGETABLEENTRY))) by { admit(); } // TODO: P0

            assert(forall |i: int| mpt.ptes@.value().contains_key(i) ==>
                    (#[trigger] mpt.ptes@.value()[i]).frame_pa != p.addr()) by { admit(); } // TODO: P0
            assert(used_addr_token@.element() == p.addr() as usize) by { admit(); } // TODO: don't know why it is not true
            instance.get().new_at(p.addr() as int, simple_page_table::FrameView {
                pa: p.addr() as int,
                pte_addrs: Set::empty(),
            }, mpt.frames.borrow_mut(), used_addr_token.get(), mpt.ptes.borrow_mut());
        }

        assume(mpt.wf()); // TODO: P0 why this fails?

        print_msg("alloc frame", used_addr);

        FakePageTableLock {
            paddr: used_addr as Paddr,
            phantom: std::marker::PhantomData,
        }
    }

    #[verifier::external_body]
    fn unlock(&mut self) -> PageTableNode<E, C> {
        todo!()
    }

    fn into_raw_paddr(self: Self) -> crate::mm::Paddr where Self: Sized {
        self.paddr
    }

    #[verifier::external_body]
    fn from_raw_paddr(paddr: crate::mm::Paddr) -> Self where Self: Sized {
        FakePageTableLock {
            paddr,
            phantom: std::marker::PhantomData,
        }
    }

    #[verifier::external_body]
    fn nr_children(&self) -> u16 {
        todo!()
    }

    fn read_pte(&self, idx: usize, mpt: &exec::MockPageTable) -> (res: E)
    ensures
        res.frame_paddr() == get_pte_from_addr_spec((self.paddr + idx * SIZEOF_PAGETABLEENTRY) as usize, mpt).frame_pa,
        res.pte_paddr() == (self.paddr + idx * SIZEOF_PAGETABLEENTRY) as usize,
    {
        assert(self.paddr + idx * SIZEOF_PAGETABLEENTRY < usize::MAX) by { admit(); } // TODO
        E::from_usize(self.paddr + idx * SIZEOF_PAGETABLEENTRY, mpt)
    }

    #[verifier::external_body]
    fn write_pte(&self, idx: usize, pte: E, mpt: &mut MockPageTable, level: crate::mm::PagingLevel) {
        let (p, Tracked(pt)) = get_frame_from_index(frame_addr_to_index(self.paddr), &mpt.mem); // TODO: permission violation
        let mut frame = p.read(Tracked(&pt));
        frame.ptes[idx] = SimplePageTableEntry {
            pte_addr: pte.pte_paddr() as u64,
            frame_pa: pte.frame_paddr() as u64,
            level: level as u8,
        };
        println!("write_pte: paddr = 0x{:x}, idx = {1}, frame_pa = 0x{2:x}, level = {3}", self.paddr, idx, pte.frame_paddr(), level);
        p.write(Tracked(&mut pt), frame);
    }

    #[verifier::external_body]
    fn meta(&self) -> &PageTablePageMeta<E, C> {
        unimplemented!("meta")
    }

    // #[verifier::external_body]
    // fn nr_children_mut(&mut self) -> &mut u16 {
    //     todo!()
    // }

    #[verifier::external_body]
    fn change_children(&self, delta: i16) {
        // TODO: implement this function
    }

    #[verifier::external_body]
    fn is_tracked(&self) -> crate::mm::MapTrackingStatus {
        crate::mm::MapTrackingStatus::Tracked
    }

    open spec fn paddr_spec(&self) -> Paddr {
        self.paddr as Paddr
    }

    #[verifier::external_body]
    fn level(&self) -> crate::mm::PagingLevel {
        todo!()
    }

}

struct_with_invariants!{
    pub struct MockPageTable {
        pub mem: HashMap<usize, (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>)>, // mem is indexed by index!
        pub frames: Tracked<simple_page_table::SimplePageTable::frames>, // frame is indexed by paddr!
        pub ptes: Tracked<simple_page_table::SimplePageTable::ptes>,
        pub instance: Tracked<simple_page_table::SimplePageTable::Instance>,

        // pub unused_addrs: Tracked<simple_page_table::SimplePageTable::unused_addrs>,
        // pub unused_pte_addrs: Tracked<simple_page_table::SimplePageTable::unused_pte_addrs>,
    }

    pub open spec fn wf(&self) -> bool {
        predicate {
        &&& self.frames@.instance_id() == self.instance@.id()
        &&& self.ptes@.instance_id() == self.instance@.id()
        &&& self.mem.len() == MAX_FRAME_NUM
        &&& self.mem@.dom().finite()
        &&& forall |i: usize| 0 <= i < MAX_FRAME_NUM ==> {
            &&& (#[trigger] self.mem@.dom().contains(i))
        }
        &&& forall |i: usize| 0 <= i < MAX_FRAME_NUM ==> {
            &&& (#[trigger] self.mem@[i]).1@.pptr() == self.mem@[i].0
        }
        &&& forall |i: usize| 0 <= i < MAX_FRAME_NUM ==> {
            &&& (#[trigger] self.mem@[i].0.addr() == PHYSICAL_BASE_ADDRESS() as usize + i * SIZEOF_FRAME)
        }
        &&& forall |i: usize| 0 <= i < MAX_FRAME_NUM ==>
                self.mem@[i].1@.mem_contents() != MemContents::<SimpleFrame>::Uninit ==>
                    #[trigger] self.frames@.value().contains_key(frame_index_to_addr(i) as int)
                    &&
                    forall |k: int| 0 <= k < NR_ENTRIES ==>
                        if ((#[trigger] self.mem@[i].1@.mem_contents().value().ptes[k]).frame_pa != 0) {
                            self.ptes@.value().contains_key(self.mem@[i].1@.mem_contents().value().ptes[k].pte_addr as int)
                        }
                        else {
                            !self.ptes@.value().contains_key(self.mem@[i].1@.mem_contents().value().ptes[k].pte_addr as int)
                        }
            // TODO: reverse relationship between ptes and frames
        }
    }
}

pub tracked struct Tokens {
    pub tracked unused_addrs: Map<int, simple_page_table::SimplePageTable::unused_addrs>,
    pub tracked unused_pte_addrs: Map<int, simple_page_table::SimplePageTable::unused_pte_addrs>,
}

pub fn test_map(va: Vaddr, frame: Frame<SimpleFrameMeta>, page_prop: page_prop::PageProperty)
requires
    0 <= va < MAX_USERSPACE_VADDR,
{
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    broadcast use vstd::hash_map::group_hash_map_axioms;
    let tracked (
        Tracked(instance),
        Tracked(frames_token),
        Tracked(unused_addrs),
        Tracked(pte_token),
        Tracked(unused_pte_addrs),
    ) = simple_page_table::SimplePageTable::Instance::initialize();
    let tracked tokens = Tokens {
        unused_addrs: unused_addrs.into_map(),
        unused_pte_addrs: unused_pte_addrs.into_map(),
    };

    // TODO: use Cursor::new
    let mut cursor =
    CursorMut::<UserMode, SimplePageTableEntry, PagingConsts, FakePageTableLock<SimplePageTableEntry, PagingConsts>> {
        0: Cursor::<UserMode, SimplePageTableEntry, PagingConsts, FakePageTableLock<SimplePageTableEntry, PagingConsts>> {
            path: Vec::new(),
            level: 4,
            guard_level: NR_LEVELS as u8,
            va: va,
            barrier_va: 0..MAX_USERSPACE_VADDR + PAGE_SIZE, // TODO: maybe cursor::new can solve this
            preempt_guard: disable_preempt(),
            _phantom: std::marker::PhantomData,
        }
    };
    assert(cursor.0.level == 4);

    let mut mock_page_table = MockPageTable {
        mem: alloc_page_table_entries(),
        frames: Tracked(frames_token),
        ptes: Tracked(pte_token),
        instance: Tracked(instance.clone()),
    };

    let mut cur_alloc_index: usize = 0; // TODO: theoretically, this should be atomic
    let (p, Tracked(pt)) = get_frame_from_index(cur_alloc_index, &mock_page_table.mem); // TODO: permission violation
    p.write(Tracked(&mut pt), SimpleFrame {
        ptes: {
            let mut ptes = [SimplePageTableEntry {
                pte_addr: 0,
                frame_pa: 0,
                level: 0,
            }; NR_ENTRIES];
            for i in 0..NR_ENTRIES {
                assert((PHYSICAL_BASE_ADDRESS() as u64 + i as u64 * SIZEOF_PAGETABLEENTRY as u64) < usize::MAX as u64) by { admit(); }; // TODO
                ptes[i] = SimplePageTableEntry {
                    pte_addr: PHYSICAL_BASE_ADDRESS() as u64 + i as u64 * SIZEOF_PAGETABLEENTRY as u64,
                    frame_pa: 0,
                    level: 4,
                };
            }
            ptes
        },
    });


    assert(pt.mem_contents() != MemContents::<SimpleFrame>::Uninit);
    assert(pt.value().ptes.len() == NR_ENTRIES);
    // assert(pt.value().ptes[0].frame_pa == 0); // TODO: P0 don't know why this fails
    assume(forall |i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] pt.value().ptes[i]).pte_addr == PHYSICAL_BASE_ADDRESS() as u64 + i as u64 * SIZEOF_PAGETABLEENTRY as u64);
    assume(forall |i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] pt.value().ptes[i]).frame_pa == 0);
    assume(forall |i: int| 0 <= i < NR_ENTRIES ==> (#[trigger] pt.value().ptes[i]).level == 4);

    assert(mock_page_table.wf());

    assert(mock_page_table.mem.len() == MAX_FRAME_NUM);
    assert(p.addr() == PHYSICAL_BASE_ADDRESS() as usize);
    assert(mock_page_table.mem@.contains_key(cur_alloc_index));

    mock_page_table.mem.remove(&cur_alloc_index);
    assert(mock_page_table.mem.len() == MAX_FRAME_NUM - 1);
    mock_page_table.mem.insert(cur_alloc_index, (p, Tracked(pt)));
    assert(mock_page_table.mem.len() == MAX_FRAME_NUM);

    assert(mock_page_table.mem@[cur_alloc_index].1@.mem_contents() != MemContents::<SimpleFrame>::Uninit);

    let (p, Tracked(pt)) = get_frame_from_index(cur_alloc_index, &mock_page_table.mem);
    assert(pt.mem_contents() != MemContents::<SimpleFrame>::Uninit);

    // assert(mock_page_table.wf()); this should fail
    proof{
        let tracked used_addr = tokens.unused_addrs.tracked_remove(p.addr()as int);

        instance.new_at(p.addr() as int, simple_page_table::FrameView {
            pa: p.addr() as int,
            pte_addrs: Set::empty(),
        }, mock_page_table.frames.borrow_mut(), used_addr, mock_page_table.ptes.borrow_mut());
    }
    assert(mock_page_table.wf());

    cur_alloc_index = cur_alloc_index + 1;

    cursor.0.path.push(None);
    cursor.0.path.push(None);
    cursor.0.path.push(None);
    cursor.0.path.push(Some(
        FakePageTableLock {
            phantom: std::marker::PhantomData,
            paddr: p.addr(),
        }
    )); // root

    assert(cursor.0.path[cursor.0.level as usize - 1].is_some());

    cursor.map::<SimpleFrameMeta>(frame, page_prop,
        Tracked(instance),
        Tracked(tokens),
        &mut mock_page_table,
        &mut cur_alloc_index
    );

    assert(cursor.0.path.len() == NR_LEVELS as usize);
    assert(forall |i: usize| 1 < i <= NR_LEVELS as usize ==> #[trigger] cursor.0.path[i as int - 1].is_some());

    let level4_index = pte_index(va, NR_LEVELS as u8);
    let level4_frame_addr = PHYSICAL_BASE_ADDRESS();
    let level4_pte = get_pte_from_addr(level4_frame_addr + level4_index * SIZEOF_PAGETABLEENTRY, &mock_page_table);

    // let level3_frame_addr = cursor.0.path[(NR_LEVELS as usize) - 2].as_ref().unwrap().paddr() as usize;
    // assert(level4_pte.frame_pa == level3_frame_addr as u64);
}

pub fn main_test() {
    let va = 0;
    let frame = Frame::<SimpleFrameMeta> {
        ptr: 0,
        _marker: std::marker::PhantomData,
    };
    let page_prop = PageProperty {
        flags: PageFlags { bits: 0 },
        cache: page_prop::CachePolicy::Uncacheable,
        priv_flags: PrivilegedPageFlags { bits: 0 },
    };

    test_map(va, frame, page_prop);
}

#[verifier::external_body]
fn alloc_page_table_entries() ->
    (res: HashMap<usize, (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>)>)
    ensures
        res@.dom().len() == MAX_FRAME_NUM,
        res@.len() == MAX_FRAME_NUM,
        res.len() == MAX_FRAME_NUM,
        forall |i:usize| 0 <= i < MAX_FRAME_NUM ==> {
            res@.dom().contains(i)
        },
        forall |i:usize| 0 <= i < MAX_FRAME_NUM ==> {
            res@.contains_key(i)
        },
        forall |i:usize| 0 <= i < MAX_FRAME_NUM ==> {
            (#[trigger] res@[i]).1@.pptr() == res@[i].0
        },
        forall |i:usize| 0 <= i < MAX_FRAME_NUM ==> {
            #[trigger] res@[i].1@.mem_contents() == MemContents::<SimpleFrame>::Uninit
        },
        forall |i:usize| 0 <= i < MAX_FRAME_NUM ==> {
            #[trigger] (res@[i]).0.addr() == PHYSICAL_BASE_ADDRESS() as usize + i * SIZEOF_FRAME
        },
        res@.dom().finite(),
{
    let mut map =
        HashMap::<usize,
            (
                PPtr<SimpleFrame>,
                Tracked<PointsTo<SimpleFrame>>
            )>::new();
    // map.insert(0, (PPtr::from_addr(0), Tracked::assume_new()));
    let p = PHYSICAL_BASE_ADDRESS();
    for i in 0..MAX_FRAME_NUM { // TODO: possible overflow for executable code
        map.insert(
            i,
            (
                PPtr::from_addr(p + i * SIZEOF_FRAME),
                Tracked::assume_new()
            )
        );
    }
    map
}

#[verifier::external_body]
fn get_frame_from_index(index: usize,
    map: &HashMap<usize, (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>)>)
     -> (res: (PPtr<SimpleFrame>, Tracked<PointsTo<SimpleFrame>>))
    requires
        0 <= index < MAX_FRAME_NUM,
        map@.dom().contains(index),
        forall |i:usize| 0 <= i < MAX_FRAME_NUM ==> {
            map@.dom().contains(i)
        },
        forall |i:usize| 0 <= i < MAX_FRAME_NUM ==> {
            (#[trigger] map@[i]).1@.pptr() == map@[i].0
        }
    ensures
        res.1@.pptr() == res.0,
        // NOTE: this is not true! && res.0.addr() == map@[index]@.0.addr()
        res.0 == map@[index].0,
        res.1 == map@[index].1,
        map@[index].1@.mem_contents() == res.1@.mem_contents(),
{
    let (p, Tracked(pt)) = map.get(&index).unwrap();
    (*p, Tracked(pt))
}

pub open spec fn get_pte_addr_from_va_frame_addr_and_level_spec(va: usize, frame_va: usize, level: u8) -> int {
    let index = pte_index(va, level);
    let pte_addr = frame_va + index * SIZEOF_PAGETABLEENTRY;
    pte_addr
}

#[verifier::inline]
pub open spec fn get_pte_from_addr_spec(addr: usize, mpt: &MockPageTable) -> (res: SimplePageTableEntry)
recommends
    mpt.wf(),
{
    if (mpt.ptes@.value().contains_key(addr as int)) {
        let pte = mpt.ptes@.value()[addr as int];
        SimplePageTableEntry {
            pte_addr: addr as u64,
            frame_pa: pte.frame_pa as u64,
            level: pte.level as u8,
        }
    } else {
        SimplePageTableEntry {
            pte_addr: addr as u64,
            frame_pa: 0,
            level: 0,
        }
    }
}

#[verifier::external_body]
#[verifier::when_used_as_spec(get_pte_from_addr_spec)]
pub fn get_pte_from_addr(addr: usize, mpt: &MockPageTable) -> (res: SimplePageTableEntry)
    requires
        0 <= addr < PHYSICAL_BASE_ADDRESS_SPEC() + SIZEOF_FRAME * NR_ENTRIES,
        (addr - PHYSICAL_BASE_ADDRESS_SPEC()) % SIZEOF_PAGETABLEENTRY as int == 0,
        // mpt.wf(),
    ensures
        res.pte_paddr() == addr as usize,
        res == get_pte_from_addr_spec(addr, mpt)
{
    let pte = PPtr::<SimplePageTableEntry>::from_addr(addr).read(Tracked::assume_new()); // TODO: permission violation
    println!("read_pte_from_addr pte_addr: {:#x}, frame_pa: {:#x}, level: {}", pte.pte_addr, pte.frame_pa, pte.level);
    pte
}

pub open spec fn frame_index_to_addr_spec(index: usize) -> usize {
    (PHYSICAL_BASE_ADDRESS_SPEC() + index * SIZEOF_FRAME) as usize
}

#[verifier::when_used_as_spec(frame_index_to_addr_spec)]
pub fn frame_index_to_addr(index: usize) -> (res: usize)
ensures
    res == frame_index_to_addr_spec(index)
{
    assert((PHYSICAL_BASE_ADDRESS_SPEC() + index * SIZEOF_FRAME) < usize::MAX) by { admit(); } // TODO
    (PHYSICAL_BASE_ADDRESS() + index * SIZEOF_FRAME) as usize
}

// TODO: can we eliminate division
pub open spec fn frame_addr_to_index_spec(addr: usize) -> usize {
    ((addr - PHYSICAL_BASE_ADDRESS_SPEC()) / SIZEOF_FRAME as int) as usize
}

pub fn frame_addr_to_index(addr: usize) -> (res: usize)
ensures
    res == frame_addr_to_index_spec(addr)
{
    assert((addr - PHYSICAL_BASE_ADDRESS()) >= 0) by { admit(); } // TODO
    ((addr - PHYSICAL_BASE_ADDRESS()) / SIZEOF_FRAME) as usize
}

pub open spec fn PHYSICAL_BASE_ADDRESS_SPEC() -> usize {
    0
}

#[allow(unused_imports)]
use std::alloc::{alloc, dealloc, Layout};

#[verifier::external_body]
#[verifier::when_used_as_spec(PHYSICAL_BASE_ADDRESS_SPEC)]
pub fn PHYSICAL_BASE_ADDRESS() -> (res: usize)
ensures
    res == PHYSICAL_BASE_ADDRESS_SPEC()
{
    static MAP: OnceLock<Mutex<usize>> = OnceLock::new();
    if MAP.get().is_none() {
        unsafe{
            let layout = Layout::new::<[FakePageTableLock<SimplePageTableEntry, PagingConsts>; 4096]>();
            let mut ptr = alloc(layout);
            MAP.set(Mutex::new(ptr as *mut u8 as usize)).unwrap();
        }

        let mut guard = MAP.get().unwrap().lock().unwrap();
        let res: usize = *guard;
        println!("PHYSICAL_BASE_ADDRESS: {:#x}", res);
    }
    let mut guard = MAP.get().unwrap().lock().unwrap();
    let res: usize = *guard;
    res
}

#[verifier::external_body]
pub fn print_msg(msg: &str, num: usize) {
    println!("{}: {:#x}", msg, num);
}

#[verifier::external_body]
pub fn print_num(num: usize) {
    println!("print_num: {:#x}", num);
}

}
