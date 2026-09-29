-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadic_exponent_eq_of_odd_cofactors
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:02:31.305426+00:00
-- url     : https://prove2.me/submissions/4346c901-a17c-463e-b755-a8f6a8ad77ab

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
theorem solution {k l d e : ℕ}
    (hd : ¬ 2 ∣ d) (he : ¬ 2 ∣ e)
    (h : 2 ^ k * d = 2 ^ l * e) : k = l := by
  have hnotlt : ∀ {a b u v : ℕ}, ¬ 2 ∣ u →
      2 ^ a * u = 2 ^ b * v → ¬ a < b := by
    intro a b u v hu huv hab
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hab)
    have heq : 2 ^ a * u = 2 ^ a * (2 * (2 ^ r * v)) := by
      rw [hr, pow_add, pow_succ] at huv
      nlinarith only [huv]
    have hcancel : u = 2 * (2 ^ r * v) :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) heq
    exact hu ⟨2 ^ r * v, hcancel⟩
  have hkl := hnotlt hd h
  have hlk := hnotlt he h.symm
  omega
