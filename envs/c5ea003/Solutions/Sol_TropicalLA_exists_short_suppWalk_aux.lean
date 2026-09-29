-- Prove2me | solution 1 for TropicalLA.exists_short_suppWalk_aux
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T09:59:47.680303+00:00
-- url     : https://prove2.me/submissions/39485723-2992-4270-9a05-2a1095ca4c57

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] {A : Matrix ι ι (WithBot ℝ)} :
    ∀ (m : ℕ), 0 < m → ∀ p : ℕ → ι, IsSuppWalk A p m →
      ∃ (m' : ℕ) (q : ℕ → ι), 0 < m' ∧ m' ≤ Fintype.card ι ∧ q 0 = p 0 ∧ q m' = p m ∧
        IsSuppWalk A q m' := by
  classical
  set N := Fintype.card ι with hN
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm p hp
    rcases Nat.lt_or_ge N m with hNm | hmN
    · have key : ∀ a b : ℕ, a < b → b ≤ N → p a = p b → ∃ (m' : ℕ) (q : ℕ → ι), 0 < m' ∧
          m' ≤ N ∧ q 0 = p 0 ∧ q m' = p m ∧ IsSuppWalk A q m' := by
        intro a b hab hbN hpab
        set d := b - a with hd
        set M := m - d with hM
        set q : ℕ → ι := fun s => if s ≤ a then p s else p (s + d) with hq
        have hqs : IsSuppWalk A q M := by
          intro t ht
          rcases lt_trichotomy t a with h | h | h
          · have := hp t (by omega)
            simp only [hq, show t ≤ a by omega, show t + 1 ≤ a by omega, if_true]
            exact this
          · have := hp b (by omega)
            simp only [hq, show t ≤ a by omega, show ¬ (t + 1 ≤ a) by omega, if_true, if_false]
            rw [show t = a by omega, hpab, show a + 1 + d = b + 1 by omega]
            exact this
          · have := hp (t + d) (by omega)
            simp only [hq, show ¬ (t ≤ a) by omega, show ¬ (t + 1 ≤ a) by omega, if_false]
            rw [show t + 1 + d = t + d + 1 by omega]
            exact this
        obtain ⟨m', q', hm', hm'N, hq'0, hq'm, hq'w⟩ := ih M (by omega) (by omega) q hqs
        refine ⟨m', q', hm', hm'N, ?_, ?_, hq'w⟩
        · rw [hq'0]
          simp only [hq, Nat.zero_le, if_true]
        · rw [hq'm]
          simp only [hq, show ¬ (M ≤ a) by omega, if_false]
          rw [show M + d = m by omega]
      obtain ⟨x, y, hxy, hpxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
        (fun s : Fin (N + 1) => p s) (by simp [hN])
      have hx := x.isLt
      have hy := y.isLt
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hxy) with h | h
      · exact key x y h (by omega) hpxy
      · exact key y x h (by omega) hpxy.symm
    · exact ⟨m, p, hm, hmN, rfl, rfl, hp⟩
