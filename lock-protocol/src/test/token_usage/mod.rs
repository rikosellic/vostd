mod spin_lock;
mod common;

use std::collections::HashMap;

use builtin::*;
use builtin_macros::*;
use state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;
use vstd::hash_map::*;

use super::super::spec::{
    common::*, utils::*,
    concrete_tree_spec::ConcreteSpec,
};

use common::*;
use spin_lock::*;

verus!{

type NodeToken = ConcreteSpec::nodes;
type CursorToken = ConcreteSpec::cursors;

pub tracked struct Cpu {
    pub cpu: Ghost<CpuId>,
    pub tracked token: Tracked<CursorToken>,
}

impl Cpu {
    pub proof fn new(cpu: CpuId, tracked token: Tracked<CursorToken>) -> (tracked s: Self)
        ensures
            s.cpu@ == cpu,
            s.token =~= token, 
    {
        Self { 
            cpu: Ghost(cpu), 
            token,
        }
    }
}

pub struct FrameAllocater;

impl FrameAllocater {
    pub fn allocate() -> Paddr { 0 }
}

pub struct Page {
    pub paddr: Paddr,
    pub lock: PageLock,
}

impl Page {
    pub open spec fn inv(&self) -> bool {
        &&& valid_paddr(self.paddr)
        // &&& self.lock.paddr == self.paddr
    }

    pub open spec fn valid_perm(&self, perm: &PagePerm) -> bool {
        self.paddr == perm.paddr
    }

    fn new(paddr: Paddr) -> (res: Self)
        requires
            valid_paddr(paddr),
        ensures
            res.inv(),
    {
        let tracked perm = PagePerm { paddr };
        let lock = PageLock::new(paddr, Tracked(perm));
        
        Self {
            paddr,
            lock,
        }
    }

    pub open spec fn offset_aligned(offset: Paddr) -> bool { true }

    pub fn read_u64(&self, offset: Paddr, perm: &PagePerm) -> u64 
        requires
            self.inv(),
            Self::offset_aligned(offset),
            self.valid_perm(perm),
    { 0 }

    pub fn write_u64(&self, offset: Paddr, val: u64, perm: Tracked<PagePerm>) -> (res: Tracked<PagePerm>)
        requires
            self.inv(),
            Self::offset_aligned(offset),
            self.valid_perm(&perm@),
        ensures
            res =~= perm,
    {
        perm
    }
}

pub struct PageTableNode {
    pub nid: Ghost<NodeId>, // NodeId of this node
    pub childs: Ghost<Seq<Option<()>>>,
    pub page: Page,
    pub tracked tokens: Tracked<Map<NodeId, NodeToken>>,
}

impl PageTableNode {
    pub open spec fn wf(&self) -> bool {
        &&& NodeHelper::valid_nid(self.nid@)
        &&& self.childs@.len() == 512
    }

    pub open spec fn valid_tokens(
        nid: NodeId, 
        childs: Seq<Option<()>>, 
        tokens: Map<NodeId, NodeToken>
    ) -> bool {
        &&& forall |_nid| tokens.dom().contains(_nid) <==> {
            ||| _nid == nid
            ||| exists |offset: nat| #![auto] {
                &&& valid_pte_offset(offset)
                &&& childs[offset as int].is_None()
                &&& NodeHelper::in_subtree(NodeHelper::get_child(nid, offset), _nid)
            }
        }

        &&& tokens[nid].value().is_Free()

        &&& forall |_nid| #![auto] _nid != nid && tokens.dom().contains(_nid) ==>
            tokens[_nid].value().is_Empty()
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.wf()
        &&& self.page.inv()
        &&& Self::valid_tokens(
            self.nid@,
            self.childs@,
            self.tokens@,
        )
    }

    pub open spec fn child_exist(&self, offset: nat) -> bool {
        self.childs@[offset as int].is_Some()
    }

    pub fn new(nid: Ghost<NodeId>, page: Page, tracked tokens: Tracked<Map<NodeId, NodeToken>>) -> (res: Self)
        requires
            NodeHelper::valid_nid(nid@),
            page.inv(),
            Self::valid_tokens(nid@, Seq::new(512, |i| Option::None), tokens@),
        ensures
            res.inv(),
    {
        Self {
            nid: Ghost(nid@),
            childs: Ghost(Seq::new(512, |i| Option::None)),
            page,
            tokens: Tracked(tokens.get()),
        }
    }

    pub fn new_from_paddr(nid: Ghost<NodeId>, paddr: Paddr, tracked tokens: Tracked<Map<NodeId, NodeToken>>) -> (res: Self)
        requires
            NodeHelper::valid_nid(nid@),
            valid_paddr(paddr@),
            Self::valid_tokens(nid@, Seq::new(512, |i| Option::None), tokens@),
        ensures
            res.inv(),
    {
        let page = Page::new(paddr);
        Self::new(nid, page, Tracked(tokens.get()))
    }
}

pub struct PageTable {
    pub nodes: HashMap<usize, PageTableNode>,
    pub tracked inst: Tracked<ConcreteSpec::Instance>,
}

impl PageTable {
    pub open spec fn wf(&self) -> bool {
        &&& forall |nid: NodeId| self.nodes@.contains_key(nid as usize) ==> NodeHelper::valid_nid(nid)
        &&& self.nodes@.contains_key(NodeHelper::root_id() as usize)
        &&& forall |nid: NodeId| #![auto] nid != NodeHelper::root_id() && NodeHelper::valid_nid(nid) ==> {
            self.nodes@.contains_key(nid as usize) ==> self.nodes@.contains_key(NodeHelper::get_parent(nid) as usize)
        }
        &&& forall |nid: NodeId| NodeHelper::valid_nid(nid) && self.nodes@.contains_key(nid as usize) ==> {
            forall |offset: nat| #![auto] valid_pte_offset(offset) && self.nodes@[nid as usize].child_exist(offset) ==>
                self.nodes@.contains_key(NodeHelper::get_child(nid, offset) as usize)
        }
    }

    pub open spec fn inv(&self) -> bool {
        &&& self.wf()
        &&& forall |nid| NodeHelper::valid_nid(nid) && self.nodes@.contains_key(nid as usize) ==>
            self.nodes@[nid as usize].inv()
    }

    pub fn new(
        tracked inst: Tracked<ConcreteSpec::Instance>,
        tracked tokens: Tracked<Map<NodeId, NodeToken>>
    ) -> (res: Self)
        requires
            forall |nid| #![auto] tokens@.dom().contains(nid) <==> NodeHelper::valid_nid(nid),
            forall |nid| #![auto] tokens@.dom().contains(nid) ==> {
                if nid == NodeHelper::root_id() {
                    tokens@[nid].value().is_Free()
                } else { 
                    tokens@[nid].value().is_Empty() 
                }
            },
        ensures
            res.inv(),
    {
        let rt_paddr = FrameAllocater::allocate();
        assert(NodeHelper::valid_nid(NodeHelper::root_id())) by {
            NodeHelper::lemma_root_id();
        };
        assert(PageTableNode::valid_tokens(0, Seq::new(512, |i| Option::None), tokens@)) by { admit(); };
        let rt_node = PageTableNode::new_from_paddr(
            Ghost(NodeHelper::root_id()),
            rt_paddr,
            Tracked(tokens.get()),
        );

        let mut nodes: HashMap<usize, PageTableNode> = HashMap::new();
        nodes.insert(0, rt_node);

        let pt = Self { nodes, inst: Tracked(inst.get()) };
        assert(pt.inv()) by { admit(); };
        pt
    }
}

fn test() {
    // Configurations
    let ghost cpu_num: nat = 2;

    // Build tokenized state machine
    let tracked inst;
    let tracked nodes_tokens;
    let tracked mut cursors_tokens;
    proof {
        let tracked (
            Tracked(inst0),
            Tracked(nodes_tokens0),
            Tracked(cursors_tokens0),
        ) = ConcreteSpec::Instance::initialize(cpu_num);

        inst = inst0;
        nodes_tokens = nodes_tokens0;
        cursors_tokens = cursors_tokens0;
    }
    let tracked_inst: Tracked<ConcreteSpec::Instance> = Tracked(inst.clone());

    assert(nodes_tokens.dom() =~= Set::new(
        |nid| NodeHelper::valid_nid(nid),
    ));
    assert(cursors_tokens.dom() =~= Set::new(
        |cpu| valid_cpu(cpu_num, cpu),
    ));

    let tracked cpu0 = Cpu::new(0, Tracked(cursors_tokens.remove(0)));
    let tracked cpu1 = Cpu::new(1, Tracked(cursors_tokens.remove(1)));
    assert(cursors_tokens.dom() =~= Set::empty());

    let mut page_table = PageTable::new(tracked_inst, Tracked(nodes_tokens.into_map()));
}

}