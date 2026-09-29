-- Prove2me | solution 1 for TropicalElimination.exists_mem_support_eq_pair
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T01:42:02.968328+00:00
-- url     : https://prove2.me/submissions/04004e8b-79bd-4544-9360-d3c6d307aca2

import Mathlib
import Definitions.Def_Tropical_TropicalLinearSpaceElimination

open TropicalElimination in
theorem solution {E : Type*} [Nontrivial E] [DecidableEq E] [Nontrivial E] [DecidableEq E]
    (c : E → TT) (hc : ∀ i, c i ≠ ⊤)
    {i j : E} (hij : i ≠ j) :
    ∃ x ∈ tropVanishing c, supp x = {i, j} := by
  -- `x = -c` on `{i, j}` and `⊤` elsewhere: the minimum `0` is attained exactly twice
  let x : E → TT := fun k => if k = i ∨ k = j then (((-(c k).untop (hc k)) : ℚ) : TT) else ⊤
  have hzero : ∀ k, k = i ∨ k = j → c k + x k = 0 := by
    intro k hk
    simp only [x, if_pos hk]
    set q := (c k).untop (hc k) with hq'
    have hq : ((q : ℚ) : TT) = c k := WithTop.coe_untop (c k) (hc k)
    rw [← hq, ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero]
  have htop : ∀ k, ((k = i ∨ k = j) → False) → c k + x k = ⊤ := by
    intro k hk
    simp only [x, if_neg hk]
    exact WithTop.add_top _
  refine ⟨x, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · refine ⟨j, ?_, ?_⟩
      · rintro rfl
        exact hij hki.symm
      · exact (hzero j (Or.inr rfl)).trans_le (hzero k (Or.inl hki)).symm.le
    · refine ⟨i, fun h => hki h.symm, ?_⟩
      by_cases hkj : k = j
      · exact (hzero i (Or.inl rfl)).trans_le (hzero k (Or.inr hkj)).symm.le
      · rw [hzero i (Or.inl rfl), htop k (by tauto)]
        exact le_top
  · ext k
    simp only [supp, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, x]
    split_ifs with h
    · simp [h, hc k]
    · simp [h]
