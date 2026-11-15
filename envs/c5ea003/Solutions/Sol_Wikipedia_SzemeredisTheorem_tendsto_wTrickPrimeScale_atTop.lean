-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.tendsto_wTrickPrimeScale_atTop
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:34:42.150966+00:00
-- url     : https://prove2.me/submissions/6c6844d0-61d2-4ee2-9be4-a0c22fce6080

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
/-- For every positive `W`, the scale `W * (N / 8)` tends to infinity with
`N`.  This is the elementary reindexing fact needed to pull back the
Chebyshev estimate. -/
theorem solution {W : ℕ} (hW : 0 < W) :
    Tendsto (wTrickPrimeScale W) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  filter_upwards [eventually_ge_atTop (8 * K)] with N hN
  have hK : K ≤ N / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < (8 : ℕ))]
    simpa [Nat.mul_comm] using hN
  have hOne : 1 ≤ W := hW
  calc
    K ≤ N / 8 := hK
    _ = 1 * (N / 8) := by simp
    _ ≤ W * (N / 8) := Nat.mul_le_mul_right (N / 8) hOne
    _ = wTrickPrimeScale W N := rfl
