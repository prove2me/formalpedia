-- Prove2me | solution 1 for SocialChoice.isMaximal_singleton_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T17:52:29.662168+00:00
-- url     : https://prove2.me/submissions/94e69a91-767c-4dbe-b17f-4fe2f152d032

import Mathlib
import Definitions.Def_Applications_SocialChoice_OrderSpectrum
open SocialChoice in
theorem solution (n : ℕ) [NeZero n] : IsMaximal ({1} : Frame n) := by
  unfold IsMaximal
  rw [eq_top_iff]
  intro x _
  -- every residue is a multiple of the atom `1`: `x = x.val • 1`
  have h1 : (1 : ZMod n) ∈ AddSubgroup.closure (({1} : Frame n) : Set (ZMod n)) :=
    AddSubgroup.subset_closure (by simp)
  have h2 := AddSubgroup.nsmul_mem _ h1 x.val
  rw [nsmul_one, ZMod.natCast_zmod_val] at h2
  exact h2
