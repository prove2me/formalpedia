-- Prove2me | solution 1 for SimpleGraph.indepRatio_eq_inv_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:37:21.09227+00:00
-- url     : https://prove2.me/submissions/d8515f0c-fe68-4b7a-929e-f5924daeb294

import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis

open SimpleGraph Finset

universe u v

open SimpleGraph Finset in
/-- **Equality case of `indepRatio ≥ 1/k`**: equality holds iff every color class is a
maximum independent set. -/
theorem solution {V : Type u} {G G₁ G₂ : SimpleGraph V} {A B : Set V} {v : V}
    (h : IsOneSum G G₁ G₂ A B v) {W : Type v} [Fintype W] (H : SimpleGraph W) {k : ℕ}
    (C : H.Coloring (Fin k)) (hpos : 0 < Fintype.card W) :
    H.indepRatio = 1 / (k : ℚ) ↔ ∀ c : Fin k, ({x | C x = c} : Finset W).card = H.indepNum := by
  classical
  have hkpos : 0 < k := by
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
    exact Fin.pos (C x)
  have hclass : ∀ c : Fin k, ({x | C x = c} : Finset W).card ≤ H.indepNum := by
    intro c
    apply SimpleGraph.IsIndepSet.card_le_indepNum
    intro x hx y hy _ hadj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    exact C.valid hadj (hx.trans hy.symm)
  have hsum : Fintype.card W = ∑ c : Fin k, ({x | C x = c} : Finset W).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (C x))
  have hn0 : (Fintype.card W : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have key : H.indepRatio = 1 / (k : ℚ) ↔ k * H.indepNum = Fintype.card W := by
    unfold SimpleGraph.indepRatio
    rw [div_eq_div_iff hn0 hk0]
    constructor
    · intro e
      have e2 : ((k * H.indepNum : ℕ) : ℚ) = (Fintype.card W : ℚ) := by push_cast; linarith
      exact_mod_cast e2
    · intro e
      have e2 : ((k * H.indepNum : ℕ) : ℚ) = (Fintype.card W : ℚ) := by exact_mod_cast e
      push_cast at e2
      linarith
  rw [key]
  constructor
  · intro e c
    have hs : ∑ c : Fin k, ({x | C x = c} : Finset W).card = ∑ _c : Fin k, H.indepNum := by
      rw [← hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, e]
    exact (Finset.sum_eq_sum_iff_of_le (fun c _ => hclass c)).mp hs c (Finset.mem_univ c)
  · intro hall
    rw [hsum, Finset.sum_congr rfl (fun c _ => hall c), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
