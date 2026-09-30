-- Prove2me | solution 1 for Finset.sum_filter_le_add_sum_filter_le_swap
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-29T19:05:31.354001+00:00
-- url     : https://prove2.me/submissions/c2d6f7e5-8ba2-4a71-8765-50169585d165

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

open Finset

theorem solution {ι M : Type*} [LinearOrder ι] [AddCommMonoid M]
    (s : Finset ι) (f : ι → ι → M)
    (hdiag : ∀ x, f x x = 0) :
    ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) +
        ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u) =
      ∑ x ∈ s, ∑ y ∈ s, f x y := by
  classical
  calc ((∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f u t) +
          ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u)
      = (∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ t < u), f t u) +
          ∑ t ∈ s, ∑ u ∈ s.filter (fun u ↦ u ≤ t), f t u := by
        rw [Finset.sum_comm' (t' := s) (s' := fun u ↦ s.filter (fun t ↦ u ≤ t))
          (by simp; tauto)]
        refine congrArg₂ _ (Finset.sum_congr rfl fun t _ ↦ (Finset.sum_subset
          (monotone_filter_right _ fun _ _ ↦ le_of_lt) fun u hu hu' ↦ ?_).symm) rfl
        simp only [mem_filter, not_and, not_lt] at hu hu'
        rw [le_antisymm (hu' hu.1) hu.2, hdiag]
    _ = ∑ x ∈ s, ∑ y ∈ s, f x y := by
        rw [add_comm, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ ↦ by
          simpa using Finset.sum_filter_add_sum_filter_not s (· ≤ x) (f x)
