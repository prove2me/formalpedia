-- Prove2me | solution 1 for SymmetryBreakingCost.QTree.card_le_two_pow_depth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:31:57.868834+00:00
-- url     : https://prove2.me/submissions/6f964b73-26c5-4d2d-b7c3-e6bee694071b

import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostAdaptive
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring
open SymmetryBreakingCost in
theorem solution : ∀ (t : QTree) (S : Finset ℕ), t.Solves S → S.card ≤ 2 ^ t.depth := by
  intro t
  induction t with
  | leaf n =>
    -- a leaf answers a single candidate
    intro S hS
    have hsub : S ⊆ {n} := fun r hr => by
      rw [Finset.mem_singleton]
      exact (hS r hr).symm
    have := Finset.card_le_card hsub
    simpa [QTree.depth] using this
  | node x t f iht ihf =>
    -- the query splits the candidates between the two subtrees
    intro S hS
    classical
    have h1 := iht (S.filter fun r => jacobiSym x r = 1) (fun r hr => by
      rw [Finset.mem_filter] at hr
      have := hS r hr.1
      simp only [QTree.run, if_pos hr.2] at this
      exact this)
    have h2 := ihf (S.filter fun r => ¬ jacobiSym x r = 1) (fun r hr => by
      rw [Finset.mem_filter] at hr
      have := hS r hr.1
      simp only [QTree.run, if_neg hr.2] at this
      exact this)
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun r => jacobiSym x r = 1)
    have ht : 2 ^ t.depth ≤ 2 ^ (max t.depth f.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
    have hf : 2 ^ f.depth ≤ 2 ^ (max t.depth f.depth) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    simp only [QTree.depth, pow_succ]
    omega
