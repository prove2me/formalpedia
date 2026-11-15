-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.card_class_mean_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:36.449491+00:00
-- url     : https://prove2.me/submissions/bdd720fa-5571-46f8-bf82-331bd25774a5

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_card_mul_log_cutoff_le_selected_log_mass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_untrickedPrimeResidues_weight

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/

namespace Wikipedia.SzemeredisTheorem













theorem wTrickedPrimeWeight_nonneg {N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 ≤ α) (W b : ℕ) (n : ZMod N) :
    0 ≤ wTrickedPrimeWeight α W b n := by
  unfold wTrickedPrimeWeight
  split_ifs with h
  · exact mul_nonneg
      (mul_nonneg hα
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h.2.ne_zero)))
  · exact le_rfl













end Wikipedia.SzemeredisTheorem

end

section






/-!
# From primes in a quarter interval to a dense W-tricked prime weight

This file supplies the finite arithmetic bridge in the `W`-trick.  We take
`X = W * (N / 8)`, choose one reduced class among the primes in `(X / 4, X]`,
and send a prime `p` in that class to `(p - b) / W`.  The generous constants
in `greenTaoInterval` make this quotient lie in `[N / 64, N / 4]`.
-/

namespace Wikipedia.SzemeredisTheorem

open Finset Real Filter
open scoped BigOperators



































/-- The full cyclic sum dominates the exact logarithmic mass of the selected
prime class. -/
theorem selected_log_mass_le_sum_wTrickedPrimeWeight
    {W N b : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α) (hW : 0 < W) :
    α * ((W.totient : ℝ) / W) *
          ∑ p ∈ quarterIntervalResidueClass W N b, log p ≤
      ∑ n : ZMod N, wTrickedPrimeWeight α W b n := by
  rw [← sum_untrickedPrimeResidues_weight α hW]
  exact Finset.sum_le_univ_sum_of_nonneg
    (wTrickedPrimeWeight_nonneg hα W b)

/-- Mean form of the exact finite logarithmic-mass lower bound. -/
theorem selected_log_mass_div_card_le_mean
    {W N b : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α) (hW : 0 < W) :
    (α * ((W.totient : ℝ) / W) *
          ∑ p ∈ quarterIntervalResidueClass W N b, log p) / N ≤
      mean (wTrickedPrimeWeight α W b : ZMod N → ℝ) := by
  rw [mean, Fintype.expect_eq_sum_div_card, ZMod.card]
  exact div_le_div_of_nonneg_right
    (selected_log_mass_le_sum_wTrickedPrimeWeight hα hW)
    (Nat.cast_nonneg N)



































end Wikipedia.SzemeredisTheorem

end
/-!
# From primes in a quarter interval to a dense W-tricked prime weight

This file supplies the finite arithmetic bridge in the `W`-trick.  We take
`X = W * (N / 8)`, choose one reduced class among the primes in `(X / 4, X]`,
and send a prime `p` in that class to `(p - b) / W`.  The generous constants
in `greenTaoInterval` make this quotient lie in `[N / 64, N / 4]`.
-/
open Wikipedia.SzemeredisTheorem
open Finset Real Filter
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- A cardinality lower bound for one prime class gives a fully explicit
lower bound for the mean W-tricked prime weight. -/
theorem solution
    {W N b : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α) (hW : 0 < W) :
    (α * ((W.totient : ℝ) / W) *
        ((#(quarterIntervalResidueClass W N b) : ℝ) *
          log (wTrickPrimeScale W N / 4 + 1 : ℕ))) / N ≤
      mean (wTrickedPrimeWeight α W b : ZMod N → ℝ) := by
  calc
    _ ≤
        (α * ((W.totient : ℝ) / W) *
          ∑ p ∈ quarterIntervalResidueClass W N b, log p) / N := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left
          card_mul_log_cutoff_le_selected_log_mass
          (mul_nonneg hα
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      · exact Nat.cast_nonneg N
    _ ≤ mean (wTrickedPrimeWeight α W b : ZMod N → ℝ) :=
      selected_log_mass_div_card_le_mean hα hW
