-- Prove2me | solution 1 for TropicalElimination.support_elimination
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T03:05:15.247992+00:00
-- url     : https://prove2.me/submissions/4c64d21c-0b47-4652-9b11-cdc337011579

import Mathlib
import Definitions.Def_Tropical_TropicalLinearSpaceElimination

open TropicalElimination in
theorem solution {E : Type*} [Nontrivial E] [Fintype E] [Nonempty E] [Fintype E] [DecidableEq E]
    [Nontrivial E] {V : Set (E → TT)} (hV : IsTropicalLinearSpace V) {x y : E → TT}
    (hx : x ∈ V) (hy : y ∈ V) {e : E} (hxe : e ∈ supp x) (hye : e ∈ supp y) :
    ∃ z ∈ V, supp z ⊆ (supp x ∪ supp y) \ {e} := by
  have hxe' : x e ≠ ⊤ := hxe
  obtain ⟨p, hpx⟩ := WithTop.ne_top_iff_exists.1 hxe'
  obtain ⟨q, hqy⟩ := WithTop.ne_top_iff_exists.1 (show y e ≠ ⊤ from hye)
  -- rescale `y` so that it agrees with `x` at `e`
  let y' := tropSMul (((p - q : ℚ)) : TT) y
  have hy' : y' ∈ V := hV.semimodule.smul_mem _ hy
  have hye2 : x e = y' e := by
    show x e = ((p - q : ℚ) : TT) + y e
    rw [← hpx, ← hqy, ← WithTop.coe_add, sub_add_cancel]
  obtain ⟨z, hz, hze, hzmin, -⟩ := hV.elimination x hx y' hy' e hye2 hxe'
  refine ⟨z, hz, fun i hi => ?_⟩
  have hi' : z i ≠ ⊤ := hi
  refine ⟨?_, ?_⟩
  · by_contra hn
    simp only [Set.mem_union, supp, Set.mem_setOf_eq, ne_eq, not_or, not_not] at hn
    have hmin : min (x i) (y' i) = ⊤ := by
      simp only [y', tropSMul, hn.1, hn.2, WithTop.add_top, min_self]
    have h5 := hzmin i
    rw [hmin] at h5
    exact hi' (top_le_iff.1 h5)
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact hi' hze
