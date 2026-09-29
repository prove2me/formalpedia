-- Prove2me | solution 1 for SimpleGraph.IsOneSum.chromaticNumber_eq_max
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:32:08.123588+00:00
-- url     : https://prove2.me/submissions/154e6ac6-ddc6-4a43-b1ba-f3c2d865a72f

import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis

open SimpleGraph

open SimpleGraph in
/-- **The chromatic number of a one-sum is the maximum of the parts' chromatic numbers.** -/
theorem solution {V : Type*} {G G₁ G₂ : SimpleGraph V} {A B : Set V} {v : V}
    (h : IsOneSum G G₁ G₂ A B v) [Fintype V] :
    G.chromaticNumber = max G₁.chromaticNumber G₂.chromaticNumber := by
  classical
  have hAB : ∀ x, x ∈ A → x ∈ B → x = v := fun x ha hb => by
    have hm : x ∈ A ∩ B := ⟨ha, hb⟩
    rw [h.inter_eq] at hm
    exact hm
  have glue : ∀ {k : ℕ}, G₁.Colorable k → G₂.Colorable k → G.Colorable k := by
    intro k h1 h2
    obtain ⟨c1⟩ := h1
    obtain ⟨c2⟩ := h2
    let σ : Equiv.Perm (Fin k) := Equiv.swap (c2 v) (c1 v)
    have hσ : σ (c2 v) = c1 v := Equiv.swap_apply_left _ _
    refine ⟨Coloring.mk (fun x => if x ∈ A then c1 x else σ (c2 x)) ?_⟩
    intro x y hxy
    show (if x ∈ A then c1 x else σ (c2 x)) ≠ (if y ∈ A then c1 y else σ (c2 y))
    rw [h.sup_eq, SimpleGraph.sup_adj] at hxy
    rcases hxy with e1 | e2
    · obtain ⟨hxA, hyA⟩ := h.left_support e1
      rw [if_pos hxA, if_pos hyA]
      exact c1.valid e1
    · obtain ⟨hxB, hyB⟩ := h.right_support e2
      have hne : x ≠ y := e2.ne
      by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
      · exact absurd ((hAB x hxA hxB).trans (hAB y hyA hyB).symm) hne
      · have hx : x = v := hAB x hxA hxB
        rw [if_pos hxA, if_neg hyA, hx, ← hσ]
        intro e
        exact c2.valid (hx ▸ e2) (σ.injective e)
      · have hy : y = v := hAB y hyA hyB
        rw [if_neg hxA, if_pos hyA, hy, ← hσ]
        intro e
        exact c2.valid (hy ▸ e2) (σ.injective e)
      · rw [if_neg hxA, if_neg hyA]
        intro e
        exact c2.valid e2 (σ.injective e)
  have hle1 : G₁ ≤ G := by rw [h.sup_eq]; exact le_sup_left
  have hle2 : G₂ ≤ G := by rw [h.sup_eq]; exact le_sup_right
  have fin : ∀ H : SimpleGraph V, H.chromaticNumber ≠ ⊤ := fun H =>
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (H.colorable_of_fintype).chromaticNumber_le
  apply le_antisymm
  · have c1 : G₁.Colorable (max G₁.chromaticNumber.toNat G₂.chromaticNumber.toNat) :=
      (G₁.colorable_chromaticNumber_of_fintype).mono (le_max_left _ _)
    have c2 : G₂.Colorable (max G₁.chromaticNumber.toNat G₂.chromaticNumber.toNat) :=
      (G₂.colorable_chromaticNumber_of_fintype).mono (le_max_right _ _)
    refine (glue c1 c2).chromaticNumber_le.trans (le_of_eq ?_)
    rw [Monotone.map_max Nat.mono_cast, ENat.coe_toNat (fin G₁), ENat.coe_toNat (fin G₂)]
  · exact max_le (SimpleGraph.chromaticNumber_mono G hle1) (SimpleGraph.chromaticNumber_mono G hle2)
