-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.cubic_difference_boundary_strips
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:38:34.818006+00:00
-- url     : https://prove2.me/submissions/0e5550c1-8c8b-4719-9bad-62729ca43416

import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_StripDecomposition
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# First-entry strips in a nested finite family

A point contributes to every later set after its first appearance. This
finite identity separates cancellation in the common interior from the
three moving boundary strips of a cubic difference.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20
open scoped BigOperators
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution {α : Type*} [DecidableEq α]
    (T : ℕ → Finset α) (hT : Monotone T) (w : α → ℝ) :
    (∑ x ∈ T 0, w x) - 3 * (∑ x ∈ T 1, w x) +
        3 * (∑ x ∈ T 2, w x) - (∑ x ∈ T 3, w x) =
      -(∑ x ∈ T 1 \ T 0, w x) + 2 * (∑ x ∈ T 2 \ T 1, w x) -
        (∑ x ∈ T 3 \ T 2, w x) := by
  have h01 := Finset.sum_sdiff (f := w) (hT (by decide : (0 : ℕ) ≤ 1))
  have h12 := Finset.sum_sdiff (f := w) (hT (by decide : (1 : ℕ) ≤ 2))
  have h23 := Finset.sum_sdiff (f := w) (hT (by decide : (2 : ℕ) ≤ 3))
  linarith
