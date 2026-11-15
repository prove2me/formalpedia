-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.untrickPrime_mem_greenTaoInterval
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:06.119202+00:00
-- url     : https://prove2.me/submissions/85852bfc-79ed-4fc0-8e1a-fc69e8abace4

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
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/

namespace Wikipedia.SzemeredisTheorem



@[simp]
theorem mem_greenTaoInterval {N n : ℕ} :
    n ∈ greenTaoInterval N ↔ N / 64 ≤ n ∧ n ≤ N / 4 := by
  simp [greenTaoInterval]























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





/-- On an actual residue class, subtracting the residue before division gives
the ordinary quotient. -/
theorem untrickPrime_eq_div {W b p : ℕ} (hW : 0 < W)
    (hmod : p % W = b) :
    untrickPrime W b p = p / W := by
  have hb : b ≤ p := by
    rw [← hmod]
    exact Nat.mod_le p W
  have hdecomp : W * (p / W) + b = p := by
    simpa [hmod] using Nat.div_add_mod p W
  have hsub : p - b = W * (p / W) := by
    omega
  rw [untrickPrime, hsub, Nat.mul_div_cancel_left _ hW]



/-- The lower endpoint `W * (N / 32)` lies below the quarter-scale cutoff. -/
theorem w_mul_div_thirtyTwo_le_scale_div_four (W N : ℕ) :
    W * (N / 32) ≤ wTrickPrimeScale W N / 4 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < (4 : ℕ))]
  have hdiv : 4 * (N / 32) ≤ N / 8 := by
    omega
  calc
    W * (N / 32) * 4 = W * (4 * (N / 32)) := by ring
    _ ≤ W * (N / 8) := Nat.mul_le_mul_left W hdiv
    _ = wTrickPrimeScale W N := rfl

























































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
/-- A prime in the selected quarter-interval class maps into the fixed
Green--Tao interval. -/
theorem solution {W N b p : ℕ}
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    untrickPrime W b p ∈ greenTaoInterval N := by
  have hdata := mem_quarterIntervalResidueClass.mp hp
  have hquot : untrickPrime W b p = p / W :=
    untrickPrime_eq_div hW hdata.2.2.2
  rw [mem_greenTaoInterval, hquot]
  constructor
  · rw [Nat.le_div_iff_mul_le hW]
    calc
      N / 64 * W ≤ W * (N / 32) := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left W (by omega)
      _ ≤ wTrickPrimeScale W N / 4 :=
        w_mul_div_thirtyTwo_le_scale_div_four W N
      _ ≤ p := hdata.2.1.le
  · have hpdiv : p / W ≤ N / 8 := by
      apply Nat.div_le_of_le_mul
      simpa [wTrickPrimeScale, Nat.mul_comm] using hdata.2.2.1
    exact hpdiv.trans (by omega)
