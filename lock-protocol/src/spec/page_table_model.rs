use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

type Paddr = u64;
type Vaddr = u64;

type Level = nat;

type NodeId = nat;

pub const CONST_MAX_NODE_ID: u64 = ;

pub open spec fn MAX_NODE_ID_SPEC() -> nat {
    CONST_MAX_NODE_ID as nat
}

#[verifier::when_used_as_spec(MAX_NODE_ID_SPEC)]
pub fn MAX_NODE_ID() -> (res: u64) 
    ensures
        res == MAX_NODE_ID_SPEC(),
{
    CONST_MAX_NODE_ID
}

pub struct PteFlag;

pub struct PteModel {
    pub pa: Paddr,
    pub flags: PteFlag,
}

pub struct PageModel {
    pub ghost ptes: Seq<Option<PteModel>>,
}

impl PageModel {

    pub open spec fn inv(&self) -> bool {
        self.ptes.len() == 512
    }

}

pub enum PageTableNodeModel {
    PageTablePage(Paddr, Level),
    Frame(Paddr, Level),
}

impl PageTableNodeModel {
    
    pub open spec fn paddr_spec(&self) -> Paddr {
        match self {
            Self::PageTablePage(pa, _) => pa,
            Self::Frame(pa, _) => pa,
        }
    }

    #[verifier::when_used_as_spec(paddr_spec)]
    pub fn paddr(&self) -> (res: Paddr)
        ensures
            res == self.paddr_spec(),
    {
        match self {
            Self::PageTablePage(pa, _) => pa,
            Self::Frame(pa, _) => pa,
        }
    }

    pub open spec fn level_spec(&self) -> Level {
        match self {
            Self::PageTablePage(_, level) => level,
            Self::Frame(_, level) => level,
        }
    }

    #[verifier::when_used_as_spec(level_spec)]
    pub fn level(&self) -> (res: Level)
        ensures
            res == self.level_spec(),
    {
        match self {
            Self::PageTablePage(_, level) => level,
            Self::Frame(_, level) => level,
        }
    }

}

pub mod Utils {

pub open spec fn valid_level(level: Level) -> bool {
    1 <= level <= 4,
}

pub open spec fn valid_nid(nid: NodeId) -> bool {
    0 <= nid < MAX_NODE_ID()
}

pub open spec fn root_id() -> NodeId {
    0
}

pub open spec fn va_level_to_nid(va: Vaddr, level: Level) -> NodeId 
    recommends
        valid_level(level),
{ /* TODO */ }

pub open spec fn nid_to_va_level(nid: NodeId) -> (va: Vaddr, level: Level) 
    recommends
        valid_nid(nid),
{ /* TODO */ }

pub open spec fn is_child(parent: NodeId, child: NodeId) -> bool
    recommends
        valid_nid(parent),
        valid_nid(child),
{ /* TODO */ }

pub open spec fn in_subtree(rt: NodeId, x: NodeId) -> bool
    recommends
        valid_nid(rt),
        valid_nid(x),
{ /* TODO */ }

pub open spec fn get_parent(nid: NodeId) -> NodeId
    recommends
        valid_nid(nid),
        nid != root_id(),
{ /* TODO */ }

pub open spec fn get_pte_idx(parent: NodeId, child: NodeId) -> int
    recommends
        valid_nid(parent),
        valid_nid(child),
        is_child(parent, child),
{ /* TODO */ }

}

tokenized_state_machine!{

#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(T))]
PageTableModel {

fields {
    #[sharding(constant)]
    pub root_pa: Paddr,

    #[sharding(map)]
    pub pages: Map<Paddr, PageModel>,

    #[sharding(map)]
    pub nodes: Map<NodeId, PageTableNodeModel>,
}

#[invariant]
pub fn inv_root(&self) -> bool {
    &&& self.nodes.contains_key(0)
    &&& self.nodes[0].paddr() == self.root_pa
    &&& self.nodes[0].level() == 4 // Check here
}

#[invariant]
pub fn inv_nid_valid(&self) -> bool {
    forall |nid: NodeId| self.nodes.contains_key(nid) ==> valid_nid(nid)
}

#[invariant]
pub fn inv_pages(&self) -> bool {
    forall |pa: Paddr| self.pages.contains_key(pa) ==> self.pages[pa].inv()
}

#[invariant]
pub fn inv_tree(&self) -> bool {
    forall |nid: NodeId| self.nodes.contains_key(nid) ==> {
        nid == Utils::root_id() || self.nodes.contains_key(Utils::get_parent(nid))
    }
}

#[invariant]
pub fn inv_level_adjacent(&self) -> bool {
    forall |x: NodeId, y: NodeId| 
        self.nodes.contains_key(x) && self.nodes.contains_key(y) && is_child(x, y) ==> {
            self.nodes[x].level() == self.nodes[y].level() + 1
        }
}

#[invariant]
pub fn inv_node_map_to_page(&self) -> bool {
    &&& forall |nid: NodeId| self.nodes.contains_key(nid) ==>
        self.pages.contains_key(self.nodes[nid].paddr())
    &&& forall |x: NodeId, y: NodeId| 
        self.nodes.contains_key(x) && self.nodes.contains_key(y) && is_child(x, y) ==> {
            &&& self.pages[self.nodes[nid].paddr()].ptes[Utils::get_pte_idx(x, y)].is_Some()
            &&& self.pages[self.nodes[nid].paddr()].ptes[Utils::get_pte_idx(x, y)].get_Some_0().pa == self.nodes[y].paddr()
        }
}

#[invariant]
pub fn inv_page_map_to_node(&self) -> bool { /* TODO */ }

}

}

}