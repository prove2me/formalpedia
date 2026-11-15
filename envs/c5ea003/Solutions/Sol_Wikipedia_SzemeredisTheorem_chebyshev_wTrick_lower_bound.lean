-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.chebyshev_wTrick_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:46:35.736094+00:00
-- url     : https://prove2.me/submissions/739b3e6e-877d-498c-9f85-d52b96175b7f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_half_le_log_quarter_cutoff_div_log
import Theorems.Thm_Wikipedia_SzemeredisTheorem_w_div_sixteen_le_scale_div

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



namespace Wikipedia.SzemeredisTheorem

open Finset Real
open Filter Asymptotics



























theorem log_two_div_four_pos : 0 < log (2 : ℝ) / 4 :=
  div_pos (Real.log_pos one_lt_two) (by norm_num)





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
/-- Uniform lower bound for the explicit Chebyshev expression used in the
W-tricked density argument. -/
theorem solution
    {W N : ℕ} (hW : 0 < W)
    {α : ℝ} (hα : 0 ≤ α)
    (hN : 16 ≤ N)
    (hscale : 16 ≤ wTrickPrimeScale W N) :
    α * log 2 / 128 ≤
      (((α / (W : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale W N : ℝ) /
            log (wTrickPrimeScale W N)) *
          log (wTrickPrimeScale W N / 4 + 1 : ℕ)) / N) := by
  let X : ℕ := wTrickPrimeScale W N
  have hWreal : (0 : ℝ) < W := by
    exact_mod_cast hW
  have hratio :
      (W : ℝ) / 16 ≤ (X : ℝ) / N := by
    exact w_div_sixteen_le_scale_div W hN
  have hscaled :
      α / 16 ≤
        (α / (W : ℝ)) * ((X : ℝ) / N) := by
    calc
      α / 16 =
          (α / (W : ℝ)) * ((W : ℝ) / 16) := by
        field_simp
      _ ≤ (α / (W : ℝ)) * ((X : ℝ) / N) :=
        mul_le_mul_of_nonneg_left hratio
          (div_nonneg hα hWreal.le)
  have hlogRatio :
      (1 / 2 : ℝ) ≤
        log (X / 4 + 1 : ℕ) / log X :=
    half_le_log_quarter_cutoff_div_log hscale
  have hlogConst : 0 ≤ log 2 / 4 :=
    log_two_div_four_pos.le
  have hscaledLog :
      (α / 16) * (log 2 / 4) ≤
        ((α / (W : ℝ)) * ((X : ℝ) / N)) *
          (log 2 / 4) :=
    mul_le_mul_of_nonneg_right hscaled hlogConst
  calc
    α * log 2 / 128 =
        ((α / 16) * (log 2 / 4)) * (1 / 2) := by
      ring
    _ ≤
        (((α / (W : ℝ)) * ((X : ℝ) / N)) *
          (log 2 / 4)) *
            (log (X / 4 + 1 : ℕ) / log X) := by
      exact mul_le_mul hscaledLog hlogRatio
        (by norm_num) (mul_nonneg
          (mul_nonneg (div_nonneg hα hWreal.le)
            (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          hlogConst)
    _ =
        (((α / (W : ℝ)) *
          (log 2 / 4 * (X : ℝ) / log X) *
          log (X / 4 + 1 : ℕ)) / N) := by
      ring
