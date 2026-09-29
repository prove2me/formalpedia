-- Prove2me | solution 1 for TropicalLA.exists_short_walk_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T08:37:18.19339+00:00
-- url     : https://prove2.me/submissions/d46a0cdb-6e07-488d-b84e-e14870293e74

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}
    (hcyc : ∀ (m : ℕ) (c : ℕ → ι), c m = c 0 → pathWeight A c m ≤ 0) :
    ∀ (m : ℕ), 0 < m → ∀ (p : ℕ → ι), ∃ (m' : ℕ) (q : ℕ → ι), 0 < m' ∧ m' ≤ Fintype.card ι ∧
      q 0 = p 0 ∧ q m' = p m ∧ pathWeight A p m ≤ pathWeight A q m' := by
  classical
  set N := Fintype.card ι with hN
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm p
    rcases Nat.lt_or_ge N m with hNm | hmN
    · have key : ∀ a b : ℕ, a < b → b ≤ N → p a = p b → ∃ (m' : ℕ) (q : ℕ → ι), 0 < m' ∧
          m' ≤ N ∧ q 0 = p 0 ∧ q m' = p m ∧ pathWeight A p m ≤ pathWeight A q m' := by
        intro a b hab hbN hpab
        set d := b - a with hd
        set M := m - d with hM
        set q : ℕ → ι := fun s => if s ≤ a then p s else p (s + d) with hq
        have hloop : ∑ s ∈ range d, A (p (a + s)) (p (a + s + 1)) ≤ 0 := by
          have h1 := hcyc d (fun s => p (a + s)) (by simp [hpab, show a + d = b by omega])
          unfold pathWeight at h1
          simpa [add_assoc] using h1
        have hsplit : pathWeight A p m = pathWeight A q M
            + ∑ s ∈ range d, A (p (a + s)) (p (a + s + 1)) := by
          unfold pathWeight
          have e1 : m = a + (d + (M - a)) := by omega
          have e2 : M = a + (M - a) := by omega
          rw [e1, Finset.sum_range_add, Finset.sum_range_add]
          conv_rhs => rw [e2, Finset.sum_range_add]
          have hA : ∑ s ∈ range a, A (q s) (q (s + 1)) = ∑ s ∈ range a, A (p s) (p (s + 1)) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            have hs' := Finset.mem_range.1 hs
            simp only [hq, show s ≤ a by omega, show s + 1 ≤ a by omega, if_true]
          have hB : ∑ s ∈ range (M - a), A (q (a + s)) (q (a + s + 1))
              = ∑ s ∈ range (M - a), A (p (a + (d + s))) (p (a + (d + s) + 1)) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            have h1 : q (a + s) = p (a + (d + s)) := by
              rcases Nat.eq_zero_or_pos s with h0 | h0
              · subst h0
                simp only [hq, add_zero, le_refl, if_true]
                rw [hpab, show a + d = b by omega]
              · simp only [hq, show ¬ (a + s ≤ a) by omega, if_false]
                congr 1
                omega
            have h2 : q (a + s + 1) = p (a + (d + s) + 1) := by
              simp only [hq, show ¬ (a + s + 1 ≤ a) by omega, if_false]
              congr 1
              omega
            rw [h1, h2]
          rw [hA, hB]
          simp only [add_assoc]
          ring
        obtain ⟨m', q', hm', hm'N, hq'0, hq'm, hq'w⟩ := ih M (by omega) (by omega) q
        refine ⟨m', q', hm', hm'N, ?_, ?_, ?_⟩
        · rw [hq'0]
          simp only [hq, Nat.zero_le, if_true]
        · rw [hq'm]
          simp only [hq, show ¬ (M ≤ a) by omega, if_false]
          rw [show M + d = m by omega]
        · rw [hsplit]
          linarith
      obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun s : Fin (N + 1) => p s) (by simp [hN])
      have hx := x.isLt
      have hy := y.isLt
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
      · exact key x y h (by omega) hpxy
      · exact key y x h (by omega) hpxy.symm
    · exact ⟨m, p, hm, hmN, rfl, rfl, le_rfl⟩
