-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.w_div_sixteen_le_scale_div
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:53.166323+00:00
-- url     : https://prove2.me/submissions/dc4f1bec-d8bf-4ae3-aa11-3d50b83dec07

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





















































/-- Past the first nontrivial block, the loss from flooring `N / 8` costs
at most a factor two. -/
theorem nat_le_sixteen_mul_div_eight
    {N : ℕ} (hN : 16 ≤ N) :
    N ≤ 16 * (N / 8) := by
  omega



















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
/-- The W-trick scale divided by `N` retains at least `W / 16` after the
floor in `N / 8`. -/
theorem solution
    (W : ℕ) {N : ℕ} (hN : 16 ≤ N) :
    (W : ℝ) / 16 ≤
      (wTrickPrimeScale W N : ℝ) / N := by
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (16 : ℕ)) hN)
  have hnat :
      W * N ≤ wTrickPrimeScale W N * 16 := by
    calc
      W * N ≤ W * (16 * (N / 8)) :=
        Nat.mul_le_mul_left W (nat_le_sixteen_mul_div_eight hN)
      _ = wTrickPrimeScale W N * 16 := by
        simp [wTrickPrimeScale]
        ring
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 16) hNreal]
  exact_mod_cast hnat
