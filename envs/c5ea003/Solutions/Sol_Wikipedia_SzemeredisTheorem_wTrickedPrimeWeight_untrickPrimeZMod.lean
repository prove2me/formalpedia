-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_untrickPrimeZMod
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:36:11.914868+00:00
-- url     : https://prove2.me/submissions/ac2b010a-1c92-41b1-94fd-2a78a6dc45fb

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_untrickPrime_mem_greenTaoInterval

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















@[simp]
theorem wTrickedPrimeWeight_eq {N : ℕ} [NeZero N]
    (α : ℝ) (W b : ℕ) (n : ZMod N)
    (hn : n.val ∈ greenTaoInterval N)
    (hp : Nat.Prime (wTrickedValue W b n)) :
    wTrickedPrimeWeight α W b n =
      α * ((W.totient : ℝ) / W) *
        Real.log (wTrickedValue W b n) := by
  simp [wTrickedPrimeWeight, hn, hp]







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

/-- Reapplying the affine `W`-trick recovers the original natural number. -/
theorem w_mul_untrickPrime_add {W b p : ℕ} (hW : 0 < W)
    (hmod : p % W = b) :
    W * untrickPrime W b p + b = p := by
  rw [untrickPrime_eq_div hW hmod]
  simpa [hmod] using Nat.div_add_mod p W





/-- The untricked parameter is a standard representative modulo `N`. -/
theorem untrickPrime_lt {W N b p : ℕ} [NeZero N]
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    untrickPrime W b p < N := by
  have hmem := mem_greenTaoInterval.mp
    (untrickPrime_mem_greenTaoInterval hW hp)
  exact hmem.2.trans_lt
    (Nat.div_lt_self (NeZero.pos N) (by norm_num))

/-- Casting an untricked parameter into `ZMod N` does not change its
standard representative. -/
@[simp]
theorem val_untrickPrimeZMod {W N b p : ℕ} [NeZero N]
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    (untrickPrimeZMod N W b p).val = untrickPrime W b p := by
  exact ZMod.val_natCast_of_lt (untrickPrime_lt hW hp)

/-- The cyclic-group affine value of the untricked parameter is the original
prime. -/
@[simp]
theorem wTrickedValue_untrickPrimeZMod {W N b p : ℕ} [NeZero N]
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    wTrickedValue W b (untrickPrimeZMod N W b p) = p := by
  rw [wTrickedValue, val_untrickPrimeZMod hW hp]
  exact w_mul_untrickPrime_add hW
    (mem_quarterIntervalResidueClass.mp hp).2.2.2

















































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
/-- Exact value of the localized prime weight on an untricked prime. -/
@[simp]
theorem solution
    {W N b p : ℕ} [NeZero N] (α : ℝ)
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    wTrickedPrimeWeight α W b (untrickPrimeZMod N W b p) =
      α * ((W.totient : ℝ) / W) * log p := by
  have hmem :
      (untrickPrimeZMod N W b p).val ∈ greenTaoInterval N := by
    simpa [val_untrickPrimeZMod hW hp] using
      untrickPrime_mem_greenTaoInterval hW hp
  have hprime :
      Nat.Prime
        (wTrickedValue W b (untrickPrimeZMod N W b p)) := by
    simpa [wTrickedValue_untrickPrimeZMod hW hp] using
      (mem_quarterIntervalResidueClass.mp hp).1
  rw [wTrickedPrimeWeight_eq α W b _ hmem hprime,
    wTrickedValue_untrickPrimeZMod hW hp]
