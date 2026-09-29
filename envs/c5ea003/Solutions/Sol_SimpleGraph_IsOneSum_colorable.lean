-- Prove2me | solution 1 for SimpleGraph.IsOneSum.colorable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T05:20:52.87371+00:00
-- url     : https://prove2.me/submissions/9787f2d9-f5fe-4936-bfe9-bb469d221ce0

import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis

open SimpleGraph

open SimpleGraph in
/-- **A one-sum of `k`-colorable graphs is `k`-colorable**: glue the colorings after
permuting the second so the two agree at the cut vertex. -/
theorem solution {V : Type*} {G G₁ G₂ : SimpleGraph V} {A B : Set V} {v : V}
    (h : IsOneSum G G₁ G₂ A B v) {k : ℕ} (h1 : G₁.Colorable k) (h2 : G₂.Colorable k) :
    G.Colorable k := by
  classical
  obtain ⟨c1⟩ := h1
  obtain ⟨c2⟩ := h2
  let σ : Equiv.Perm (Fin k) := Equiv.swap (c2 v) (c1 v)
  have hσ : σ (c2 v) = c1 v := Equiv.swap_apply_left _ _
  have hAB : ∀ x, x ∈ A → x ∈ B → x = v := fun x ha hb => by
    have hm : x ∈ A ∩ B := ⟨ha, hb⟩
    rw [h.inter_eq] at hm
    exact hm
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
