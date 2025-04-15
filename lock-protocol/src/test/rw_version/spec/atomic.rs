use builtin::*;
use builtin_macros::*;
use state_machines_macros::state_machine;
use vstd::*;
use vstd::map::*;

use super::{
    common::*,
    utils::*,
};

verus!{

state_machine!{

AtomicSpec {

fields {
    pub cpu_num: CpuId,
    pub cursors: Map<CpuId, AtomicCursorState>,
}

#[invariant]
pub fn inv_cursors(&self) -> bool {
    &&& forall |cpu: CpuId| #![auto]
        self.cursors.dom().contains(cpu) <==> valid_cpu(self.cpu_num, cpu)

    &&& forall |cpu: CpuId| #![auto] 
        self.cursors.dom().contains(cpu) &&
        self.cursors[cpu].is_Locked() ==>
            NodeHelper::valid_nid(self.cursors[cpu].get_Locked_0())
}

#[invariant]
pub fn inv_non_overlapping(&self) -> bool {
    forall |cpu1: CpuId, cpu2: CpuId| #![auto]
        cpu1 != cpu2 &&
        self.cursors.dom().contains(cpu1) &&
        self.cursors[cpu1].is_Locked() &&
        self.cursors.dom().contains(cpu2) &&
        self.cursors[cpu2].is_Locked() ==> {
            let nid1 = self.cursors[cpu1].get_Locked_0();
            let nid2 = self.cursors[cpu2].get_Locked_0();

            !NodeHelper::in_subtree(nid1, nid2) && 
            !NodeHelper::in_subtree(nid2, nid1)
        }
}

pub open spec fn all_non_overlapping(&self, nid: NodeId) -> bool 
    recommends
        NodeHelper::valid_nid(nid),
{
    forall |cpu: CpuId| #![auto] 
        self.cursors.dom().contains(cpu) &&
        self.cursors[cpu].is_Locked() ==> {
            let _nid = self.cursors[cpu].get_Locked_0();

            !NodeHelper::in_subtree(nid, _nid) && 
            !NodeHelper::in_subtree(_nid, nid)
        }
}

init!{
    initialize(cpu_num: CpuId) {
        init cpu_num = cpu_num;
        init cursors = Map::new(
            |cpu| valid_cpu(cpu_num, cpu),
            |cpu| AtomicCursorState::Void,
        );
    }
}

transition!{
    lock(cpu: CpuId, nid: NodeId) {
        require(valid_cpu(pre.cpu_num, cpu));
        require(NodeHelper::valid_nid(nid));

        require(pre.cursors[cpu].is_Void());
        require(pre.all_non_overlapping(nid));
        let new_cursor = AtomicCursorState::Locked(nid);
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    unlock(cpu: CpuId) {
        require(valid_cpu(pre.cpu_num, cpu));

        require(pre.cursors[cpu].is_Locked());
        let new_cursor = AtomicCursorState::Void;
        update cursors = pre.cursors.insert(cpu, new_cursor);
    }
}

transition!{
    no_op() {}
}

#[inductive(initialize)]
fn initialize_inductive(post: Self, cpu_num: CpuId) {}

#[inductive(lock)]
fn lock_inductive(pre: Self, post: Self, cpu: CpuId, nid: NodeId) {}

#[inductive(unlock)]
fn unlock_inductive(pre: Self, post: Self, cpu: CpuId) {}

#[inductive(no_op)]
fn no_op_inductive(pre: Self, post: Self) {}

}

}

type State = AtomicSpec::State;
type Step = AtomicSpec::Step;

// Lemmas

pub proof fn lemma_mutual_exclusion(
    s1: State, s2: State, s3: State, cpu: CpuId, nid: NodeId
)
    requires
        s1.invariant(),
        s2.invariant(),
        s3.invariant(),
        State::next_by(s1, s2, Step::lock(cpu, nid)),
    ensures
        forall |step: Step| 
            State::next_by(s2, s3, step) &&
            !step.is_unlock() &&
            !step.is_no_op() &&
            !step.is_dummy_to_use_type_params() ==> {
                let _nid = step.get_lock_1();

                !NodeHelper::in_subtree(nid, _nid) &&
                !NodeHelper::in_subtree(_nid, nid)
            }
{
    reveal(AtomicSpec::State::next_by);
}

}