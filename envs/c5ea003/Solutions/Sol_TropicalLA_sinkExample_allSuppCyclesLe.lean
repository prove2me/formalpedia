-- Prove2me | solution 1 for TropicalLA.sinkExample_allSuppCyclesLe
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:18:23.659535+00:00
-- url     : https://prove2.me/submissions/1a417eec-da5b-424d-a321-2843f50ae888

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible
open TropicalLA in
theorem solution : AllSuppCyclesLe sinkExample 0 := by
  intro m p hwalk hclosed
  -- only column `0` of the example is finite, so every support step lands at `0`
  have hsupp : ∀ i j : Fin 2, Supp sinkExample i j → j = 0 := by
    intro i j h
    by_contra hj
    exact h (by simp [sinkExample, hj])
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [pathWeight]
  have hpt : ∀ t, t < m → p (t + 1) = 0 := fun t ht => hsupp _ _ (hwalk t ht)
  have hp0 : p 0 = 0 := by
    rw [← hclosed]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact hpt k (by omega)
  have hp : ∀ t, t ≤ m → p t = 0 := by
    intro t ht
    cases t with
    | zero => exact hp0
    | succ t => exact hpt t (by omega)
  -- a closed support walk just loops at the sink, whose weight is `0`
  have hf : finPart sinkExample 0 0 = 0 := by simp [finPart, sinkExample]
  unfold pathWeight
  rw [Finset.sum_eq_zero fun t ht => by
    rw [Finset.mem_range] at ht
    rw [hp t (by omega), hp (t + 1) (by omega), hf]]
  simp
