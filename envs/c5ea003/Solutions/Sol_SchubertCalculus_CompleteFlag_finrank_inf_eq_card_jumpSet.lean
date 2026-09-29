-- Prove2me | solution 1 for SchubertCalculus.CompleteFlag.finrank_inf_eq_card_jumpSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:41:34.669894+00:00
-- url     : https://prove2.me/submissions/86d9c702-d1a2-47ed-9628-58446219df54

import Mathlib
import Definitions.Def_Geometry_SchubertCalculus_Flags

open SchubertCalculus Module Submodule CompleteFlag in
theorem solution {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (Fl : CompleteFlag K V n) [FiniteDimensional K V] (W : Submodule K V) {j : ℕ} (hj : j ≤ n) :
    finrank K ((W ⊓ Fl.part j : Submodule K V)) =
      ((Fl.jumpSet W).filter fun i => i < j).card := by
  -- consecutive intersections grow by at most one dimension
  have hstep : ∀ i, i < n → finrank K ((W ⊓ Fl.part (i + 1) : Submodule K V))
      ≤ finrank K ((W ⊓ Fl.part i : Submodule K V)) + 1 := by
    intro i hi
    have hle : Fl.part i ≤ Fl.part (i + 1) := Fl.mono (Nat.le_succ i)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ Fl.part (i + 1)) (Fl.part i)
    have h2 : (W ⊓ Fl.part (i + 1)) ⊓ Fl.part i = W ⊓ Fl.part i := by
      rw [inf_assoc, inf_eq_right.2 hle]
    have h3 : (W ⊓ Fl.part (i + 1)) ⊔ Fl.part i ≤ Fl.part (i + 1) := sup_le inf_le_right hle
    have h4 := Submodule.finrank_mono h3
    rw [h2, Fl.finrank_part i (by omega)] at h1
    rw [Fl.finrank_part (i + 1) (by omega)] at h4
    omega
  have hmono : ∀ i, finrank K ((W ⊓ Fl.part i : Submodule K V))
      ≤ finrank K ((W ⊓ Fl.part (i + 1) : Submodule K V)) := fun i =>
    Submodule.finrank_mono (inf_le_inf_left W (Fl.mono (Nat.le_succ i)))
  induction j with
  | zero =>
    have h0 : Fl.part 0 = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      exact Fl.finrank_part 0 (Nat.zero_le n)
    simp [h0]
  | succ j ih =>
    have hjn : j < n := by omega
    have ih' := ih (by omega)
    -- the count up to `j + 1` adds the indicator of a jump at `j`
    have hsplit : (Fl.jumpSet W).filter (fun i => i < j + 1)
        = (Fl.jumpSet W).filter (fun i => i < j) ∪ (Fl.jumpSet W).filter (fun i => i = j) := by
      rw [← Finset.filter_or]
      apply Finset.filter_congr
      intro i _
      constructor
      · intro h
        omega
      · intro h
        omega
    have hdisj : Disjoint ((Fl.jumpSet W).filter (fun i => i < j))
        ((Fl.jumpSet W).filter (fun i => i = j)) := by
      rw [Finset.disjoint_filter]
      intro i _ h1 h2
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.filter_eq', ← ih']
    by_cases hjump : j ∈ Fl.jumpSet W
    · rw [if_pos hjump, Finset.card_singleton]
      exact (Finset.mem_filter.1 hjump).2
    · rw [if_neg hjump, Finset.card_empty, add_zero]
      have hnot : ¬ (finrank K ((W ⊓ Fl.part (j + 1) : Submodule K V))
          = finrank K ((W ⊓ Fl.part j : Submodule K V)) + 1) := fun h =>
        hjump (Finset.mem_filter.2 ⟨Finset.mem_range.2 hjn, h⟩)
      have h5 := hstep j hjn
      have h6 := hmono j
      omega
