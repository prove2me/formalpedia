-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.nested_finite_strip_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:52:59.447987+00:00
-- url     : https://prove2.me/submissions/857cea6e-b7f5-417f-bf05-256c1c4e2acc

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



theorem sum_entryStrips {α : Type*} [DecidableEq α]
    (T : ℕ → Finset α) (hT : Monotone T) (f : α → ℝ) (n : ℕ) :
    (∑ s ∈ Finset.range (n + 1), ∑ x ∈ entryStrip T s, f x) =
      ∑ x ∈ T n, f x := by
  induction n with
  | zero => simp [entryStrip]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simpa only [entryStrip, add_comm] using
      (Finset.sum_sdiff (f := f) (hT (Nat.le_succ n)))
end ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution {α : Type*} [DecidableEq α]
    (T : ℕ → Finset α) (hT : Monotone T) (F : ℕ → α → ℝ) (σ : ℕ) :
    (∑ ν ∈ Finset.range (σ + 1), ∑ x ∈ T ν, F ν x) =
      ∑ s ∈ Finset.range (σ + 1), ∑ x ∈ entryStrip T s,
        ∑ ν ∈ Finset.Icc s σ, F ν x := by
  calc
    (∑ ν ∈ Finset.range (σ + 1), ∑ x ∈ T ν, F ν x) =
        ∑ ν ∈ Finset.range (σ + 1), ∑ s ∈ Finset.range (ν + 1),
          ∑ x ∈ entryStrip T s, F ν x := by
      apply Finset.sum_congr rfl
      intro ν _
      exact (sum_entryStrips T hT (F ν) ν).symm
    _ = ∑ s ∈ Finset.range (σ + 1), ∑ ν ∈ Finset.Ico s (σ + 1),
        ∑ x ∈ entryStrip T s, F ν x := by
      simpa only [Nat.Ico_zero_eq_range] using
        (Finset.sum_Ico_Ico_comm 0 (σ + 1)
          (fun s ν => ∑ x ∈ entryStrip T s, F ν x)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp only [Finset.Ico_add_one_right_eq_Icc]
