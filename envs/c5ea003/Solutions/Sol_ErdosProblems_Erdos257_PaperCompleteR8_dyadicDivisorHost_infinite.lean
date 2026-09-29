-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadicDivisorHost_infinite
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:07:23.174895+00:00
-- url     : https://prove2.me/submissions/2133c574-1b9d-4322-8b9c-db1199d98e40

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_dyadic_exponent_eq_of_odd_cofactors
import Mathlib

/-! # Disjoint dyadic divisor frames for the weighted separating host

These are the actual frames F_k = {2^(k+2) d : d divides M_k}. Positive odd
M_k make them pairwise disjoint and give an infinite positive union. The
prime-block harmonic bounds, weighted summability and divergent logarithmic
means are further obligations, not hypotheses hidden in a class-separation
conclusion.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (M : ℕ → ℕ) (hM : ∀ k, 0 < M k) :
    (dyadicDivisorHost M).Infinite := by
  have hi : Function.Injective (fun k : ℕ => 2 ^ (k + 2)) := by
    intro k l h
    have hh := dyadic_exponent_eq_of_odd_cofactors
      (by decide : ¬ 2 ∣ 1) (by decide : ¬ 2 ∣ 1)
      (by simpa only [mul_one] using h)
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro a ⟨k, rfl⟩
  refine ⟨k, Finset.mem_image.mpr ⟨1, ?_, by simp⟩⟩
  exact Nat.one_mem_divisors.mpr (hM k).ne'
