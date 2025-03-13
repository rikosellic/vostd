use vstd::prelude::*;
use aster_common::prelude::*;
use super::*;

verus! {

impl Frame{

pub open spec fn relate_model(&self, model: PageModel) -> bool
{
    &&& self.page.relate_model(model)
    &&& model.state == PageState::Untyped
    &&& model.usage == PageUsage::Frame
    &&& exists |thread_id:int| #[trigger] model.owners.contains(PageOwner::User{thread_id})
}

#[verifier::inline]
pub open spec fn has_valid_paddr(&self) -> bool
{
    self.page.has_valid_paddr()
}

}

}
