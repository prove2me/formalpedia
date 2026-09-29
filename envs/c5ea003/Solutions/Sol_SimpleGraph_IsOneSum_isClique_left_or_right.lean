-- Prove2me | solution 1 for SimpleGraph.IsOneSum.isClique_left_or_right
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:15:25.219964+00:00
-- url     : https://prove2.me/submissions/085172a6-cddf-4a7d-8f61-b2e6d3528860

import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis

open SimpleGraph

open SimpleGraph in
/-- **A clique of a one-sum lies in one of the parts.** -/
theorem solution {V : Type*} {G G₁ G₂ : SimpleGraph V} {A B : Set V} {v : V}
    (h : IsOneSum G G₁ G₂ A B v) {s : Set V} (hs : G.IsClique s) :
    G₁.IsClique s ∨ G₂.IsClique s := by

  have hadj : ∀ ⦃x y : V⦄, x ∈ s → y ∈ s → x ≠ y → G₁.Adj x y ∨ G₂.Adj x y := by
    intro x y hx hy hxy
    have hxy' := hs hx hy hxy
    rw [h.sup_eq] at hxy'
    exact hxy'
  have hAB : ∀ x, x ∈ A → x ∈ B → x = v := fun x ha hb => by
    have hm : x ∈ A ∩ B := ⟨ha, hb⟩
    rw [h.inter_eq] at hm
    exact hm
  by_cases hsA : s ⊆ A
  · left

    intro x hx y hy hxy
    rcases hadj hx hy hxy with h1 | h2
    · exact h1
    · exfalso
      exact hxy ((hAB x (hsA hx) (h.right_support h2).1).trans
        (hAB y (hsA hy) (h.right_support h2).2).symm)
  · by_cases hsB : s ⊆ B
    · right

      intro x hx y hy hxy
      rcases hadj hx hy hxy with h1 | h2
      · exfalso
        exact hxy ((hAB x (h.left_support h1).1 (hsB hx)).trans
          (hAB y (h.left_support h1).2 (hsB hy)).symm)
      · exact h2
    · exfalso
      obtain ⟨a, ha, haA⟩ := Set.not_subset.mp hsA
      obtain ⟨b, hb, hbB⟩ := Set.not_subset.mp hsB
      have haB : a ∈ B := by
        have hu : a ∈ A ∪ B := by rw [h.union_eq]; trivial
        exact hu.resolve_left haA
      have hbA : b ∈ A := by
        have hu : b ∈ A ∪ B := by rw [h.union_eq]; trivial
        exact hu.resolve_right hbB
      have hab : a ≠ b := fun e => haA (e ▸ hbA)
      rcases hadj ha hb hab with h1 | h2
      · exact haA (h.left_support h1).1
      · exact hbB (h.right_support h2).2
