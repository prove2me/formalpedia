-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.card_mul_log_cutoff_le_selected_log_mass
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:07:40.722201+00:00
-- url     : https://prove2.me/submissions/9a1dc31e-96f9-416c-b2a1-7fbe79c777ea

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



namespace Wikipedia.SzemeredisTheorem

open Finset Real
open Filter Asymptotics



@[simp]
theorem mem_primesInQuarterInterval {X p : ℕ} :
    p ∈ primesInQuarterInterval X ↔
      p.Prime ∧ X / 4 < p ∧ p ≤ X := by
  simp [primesInQuarterInterval, and_left_comm, and_comm]





























end Wikipedia.SzemeredisTheorem

end

section





namespace Wikipedia.SzemeredisTheorem

open Finset











@[simp]
theorem mem_residueFiber {S : Finset ℕ} {W b n : ℕ} :
    n ∈ residueFiber S W b ↔ n ∈ S ∧ n % W = b := by
  simp [residueFiber]















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





@[simp]
theorem mem_quarterIntervalResidueClass {W N b p : ℕ} :
    p ∈ quarterIntervalResidueClass W N b ↔
      p.Prime ∧
        wTrickPrimeScale W N / 4 < p ∧
        p ≤ wTrickPrimeScale W N ∧
        p % W = b := by
  simp only [quarterIntervalResidueClass, mem_residueFiber,
    mem_primesInQuarterInterval]
  tauto



































































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
/-- Every prime in the selected class contributes at least the logarithm of
the first integer strictly above the quarter-scale cutoff. -/
theorem solution
    {W N b : ℕ} :
    (#(quarterIntervalResidueClass W N b) : ℝ) *
        log (wTrickPrimeScale W N / 4 + 1 : ℕ) ≤
      ∑ p ∈ quarterIntervalResidueClass W N b, log p := by
  calc
    (#(quarterIntervalResidueClass W N b) : ℝ) *
          log (wTrickPrimeScale W N / 4 + 1 : ℕ) =
        ∑ _p ∈ quarterIntervalResidueClass W N b,
          log (wTrickPrimeScale W N / 4 + 1 : ℕ) := by simp
    _ ≤ ∑ p ∈ quarterIntervalResidueClass W N b, log p := by
      apply Finset.sum_le_sum
      intro p hp
      apply Real.log_le_log
      · positivity
      · exact_mod_cast Nat.succ_le_iff.mpr
          (mem_quarterIntervalResidueClass.mp hp).2.1
