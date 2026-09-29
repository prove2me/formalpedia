-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.zero_not_mem_dyadicDivisorHost
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:39:20.057112+00:00
-- url     : https://prove2.me/submissions/c6c1e289-c517-40d7-afd8-0e02f3953681

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_DyadicDivisorFrames
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
theorem solution (M : ℕ → ℕ) :
    0 ∉ dyadicDivisorHost M := by
  rintro ⟨k, hk⟩
  obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hk
  have hp : 0 < 2 ^ (k + 2) * d :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pos_of_mem_divisors hd)
  omega
