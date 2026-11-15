-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.half_le_log_quarter_cutoff_div_log
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:11:52.535612+00:00
-- url     : https://prove2.me/submissions/1a45fc19-038f-4e95-9859-90d88973bbb9

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























































/-- For `X ≥ 16`, the integer just above `X / 4` has square at least `X`.
This is a convenient floor-safe input to the logarithmic ratio estimate. -/
theorem le_div_four_add_one_sq
    {X : ℕ} (hX : 16 ≤ X) :
    X ≤ (X / 4 + 1) ^ 2 := by
  have hquot : 4 ≤ X / 4 := by
    omega
  have hupper : X ≤ 4 * (X / 4) + 3 := by
    omega
  nlinarith

















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
/-- The logarithm at the quarter-scale cutoff retains at least half of
`log X` once `X ≥ 16`. -/
theorem solution
    {X : ℕ} (hX : 16 ≤ X) :
    (1 / 2 : ℝ) ≤
      log (X / 4 + 1 : ℕ) / log X := by
  have hXreal : (1 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (16 : ℕ)) hX)
  have hlogX : 0 < log (X : ℝ) :=
    Real.log_pos hXreal
  have hsqReal :
      (X : ℝ) ≤ ((X / 4 + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast le_div_four_add_one_sq hX
  have hlog :
      log (X : ℝ) ≤
        log (((X / 4 + 1 : ℕ) : ℝ) ^ 2) :=
    Real.log_le_log (by positivity) hsqReal
  rw [Real.log_pow] at hlog
  rw [le_div_iff₀ hlogX]
  norm_num [Nat.cast_add] at hlog ⊢
  linarith
