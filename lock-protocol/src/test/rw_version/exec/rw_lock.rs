use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;
use vstd::atomic_with_ghost;
use vstd::invariant::InvariantPredicate;
use vstd::rwlock::{
    RwLockToks,
    RwLockPredicate,
};
use vstd::tokens::{
    InstanceId,
    KeyValueToken,
};

use super::{
    common::*,
    types::*,
};

verus!{

ghost struct InternalPred<Token, Pred> {
    token: Token,
    pred: Pred,
}

impl<Token: KeyValueToken, Pred: RwLockPredicate<Token>> 
    InvariantPredicate<(Pred, InstanceId, NodeId), Token> for InternalPred<Token, Pred> {
    closed spec fn inv(k: (Pred, InstanceId, NodeId), tok: Token) -> bool {
        &&& tok.instance_id() == k.1 
        &&& token.key() == k.2
        &&& k.0.inv(token.value())
    }
}

struct_with_invariants!{
    pub struct RwLock<Token: KeyValueToken, Pred: RwLockPredicate<Token>> {
        nid: Ghost<NodeId>,
        spec_inst: Tracked<SpecInstance>,
        exc: AtomicBool<_, RwLockToks::flag_exc<(Pred, InstanceId, NodeId), Token, InternalPred<Token, Pred>>, _>,
        rc: AtomicU64<_, RwLockToks::flag_rc<(Pred, InstanceId, NodeId), Token, InternalPred<Token, Pred>>, _>,

        inst: Tracked<RwLockToks::Instance<(Pred, InstanceId, NodeId), Token, InternalPred<Token, Pred>>>,
        pred: Ghost<Pred>,
    }

    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        invariant on exc with (inst) is (v: bool, g: RwLockToks::flag_exc<(Pred, InstanceId, NodeId), Token, InternalPred<Token, Pred>>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }

        invariant on rc with (inst) is (v: u64, g: RwLockToks::flag_rc<(Pred, InstanceId, NodeId), Token, InternalPred<Token, Pred>>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }

        predicate {
            self.inst@.k() == (self.pred@, self.spec_inst@.id(), self.nid@)
        }
    }
}

}