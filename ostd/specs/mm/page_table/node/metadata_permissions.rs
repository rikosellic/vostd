use vstd::prelude::*;

verus! {

/// A mutable partition of the raw-token store. Splitting out a shared loan
/// freezes only the selected token, not the recursive subtree or other slots.
/// The backing map must outlive every `FrameRef` built from a loan. In
/// particular, a loaned token cannot be removed to restore an owning `Frame`
/// until those borrows end; this type does not circumvent that restriction.
///
/// The borrow/writeback mechanism is independent of the token representation;
/// the page-table instantiation uses `Paddr` and `FrameRawPerms`.
pub tracked struct MetadataPermissionPartition<'a, K, P> {
    pub permissions: &'a mut Map<K, P>,
}

impl<'a, K, P> MetadataPermissionPartition<'a, K, P> {
    /// Parks an already-transferred token without replacing an existing count.
    pub proof fn tracked_insert(tracked self, key: K, tracked permission: P) -> (tracked result: Self)
        requires
            !self.permissions.contains_key(key),
        ensures
            *result.permissions == old(self.permissions).insert(key, permission),
            mut_ref_future(self.permissions) == mut_ref_future(result.permissions),
    {
        self.permissions.tracked_insert(key, permission);
        self
    }

    /// Removes the original raw token for restoration into an owning handle.
    pub proof fn tracked_remove(tracked self, key: K) -> (tracked (permission, remainder): (P, Self))
        requires
            self.permissions.contains_key(key),
        ensures
            permission == (*old(self.permissions))[key],
            *remainder.permissions == old(self.permissions).remove(key),
            mut_ref_future(self.permissions) == mut_ref_future(remainder.permissions),
    {
        let tracked permission = self.permissions.tracked_remove(key);
        (permission, self)
    }

    /// Borrows a stable map slot and returns the independently mutable rest.
    /// Moving the returned partition or a recursive owner does not move the
    /// token backing `permission`; writeback rejoins the maps at borrow end.
    pub proof fn tracked_borrow(
        tracked self,
        key: K,
    ) -> (tracked (permission, remainder): (&'a P, Self))
        requires
            self.permissions.contains_key(key),
        ensures
            *permission == (*old(self.permissions))[key],
            *remainder.permissions == old(self.permissions).remove_keys(set![key]),
            mut_ref_future(self.permissions) == Map::empty().insert(key, *permission)
                .union_prefer_right(mut_ref_future(remainder.permissions)),
    {
        let tracked (slot, permissions) = self.permissions.tracked_borrow_mut_split(set![key]);
        let tracked permission = slot.tracked_borrow(key);
        (permission, Self { permissions })
    }

    /// Parks a transferred token and immediately lends it for a returned guard.
    pub proof fn tracked_insert_and_borrow(
        tracked self,
        key: K,
        tracked permission: P,
    ) -> (tracked (loan, remainder): (&'a P, Self))
        requires
            !self.permissions.contains_key(key),
        ensures
            *loan == permission,
            *remainder.permissions == *old(self.permissions),
            mut_ref_future(self.permissions) == Map::empty().insert(
                key, permission,
            ).union_prefer_right(mut_ref_future(remainder.permissions)),
    {
        let tracked partition = self.tracked_insert(key, permission);
        partition.tracked_borrow(key)
    }
}

} // verus!
