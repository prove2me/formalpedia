-- Prove2me | solution 1 for HTree.pathMargins_bound_implies_pathDominates
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T18:46:00.14969+00:00
-- url     : https://prove2.me/submissions/9b88a6ee-9f24-404d-883c-1bfc7a0fbbdf

import Mathlib
import Definitions.Def_Bridges_GraphTheory_HTreeDefs
import Definitions.Def_Bridges_GraphTheory_HTreePathMargin
import Definitions.Def_Bridges_HTreeRobust
open HTree in
theorem solution {α : Type} [DecidableEq α]
    (T : HTree α) (s : α → ℝ) (δ : ℝ)
    (hbound : ∀ m ∈ T.pathMargins s, δ < m) :
    T.PathDominates s δ := by
  -- the tournament winner maximises the score over the subtree's classes
  have hmax : ∀ (T : HTree α), ∀ c ∈ T.classes, s c ≤ s (T.eval s) := by
    intro T
    induction T with
    | leaf a =>
      intro c hc
      simp only [HTree.classes, Finset.mem_singleton] at hc
      subst hc
      simp [HTree.eval]
    | node L R ihL ihR =>
      intro c hc
      simp only [HTree.classes, Finset.mem_union] at hc
      simp only [HTree.eval]
      split_ifs with h
      · rcases hc with hc | hc
        · exact ihL c hc
        · exact (ihR c hc).trans h
      · replace h := lt_of_not_ge h
        rcases hc with hc | hc
        · exact (ihL c hc).trans h.le
        · exact ihR c hc
  induction T with
  | leaf a => simp [HTree.PathDominates]
  | node L R ihL ihR =>
    simp only [HTree.pathMargins, List.mem_cons] at hbound
    have h0 := hbound _ (Or.inl rfl)
    simp only [HTree.PathDominates]
    split_ifs with h
    · rw [if_pos h] at hbound
      rw [abs_of_nonneg (by linarith)] at h0
      refine ⟨fun c hc => ?_, ihL (fun m hm => hbound m (Or.inr hm))⟩
      have := hmax R c hc
      linarith
    · rw [if_neg h] at hbound
      replace h := lt_of_not_ge h
      rw [abs_of_neg (by linarith)] at h0
      refine ⟨fun c hc => ?_, ihR (fun m hm => hbound m (Or.inr hm))⟩
      have := hmax L c hc
      linarith
