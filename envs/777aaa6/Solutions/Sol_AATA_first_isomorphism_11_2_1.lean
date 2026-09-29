-- Prove2me | solution 1 for AATA.first_isomorphism_11_2_1
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:10:13.394854+00:00
-- url     : https://prove2.me/submissions/cea54d47-f885-41ed-a270-16e5fe05e5d6

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u v

theorem solution {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f.ker.Normal ∧ ∃! e : G ⧸ f.ker ≃* f.range,
      ∀ g : G, e (QuotientGroup.mk' f.ker g) = f.rangeRestrict g := by
  refine ⟨inferInstance, ?_⟩
  refine ⟨QuotientGroup.quotientKerEquivRange f, ?_, ?_⟩
  · intro g
    rfl
  · intro e he
    apply MulEquiv.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    exact he g
