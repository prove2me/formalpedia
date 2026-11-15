-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_reducedResidue_chebyshev_mean_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:53:30.030407+00:00
-- url     : https://prove2.me/submissions/b76550b0-0fd8-4f9e-b6db-f79c908a643d

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_reducedResidue_mean_lower_bound

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
/-- Insert the quantitative Chebyshev estimate at
`X = primorial w * (N / 8)` into the exact finite bridge. -/
theorem solution
    {w N : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α)
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4)
    (hchebyshev :
      log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
          log (wTrickPrimeScale (primorial w) N) ≤
        (#(primesInQuarterInterval
          (wTrickPrimeScale (primorial w) N)) : ℝ)) :
    ∃ b ∈ reducedResidues (primorial w),
      (((α / (primorial w : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N)) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) ≤
        mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) := by
  obtain ⟨b, hb, hmean⟩ :=
    exists_reducedResidue_mean_lower_bound hα hw
  refine ⟨b, hb, ?_⟩
  let L : ℝ :=
    log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by
      exact_mod_cast
        (show 1 ≤ wTrickPrimeScale (primorial w) N / 4 + 1 by omega))
  have hscale : 0 ≤ (α / (primorial w : ℝ)) * L :=
    mul_nonneg
      (div_nonneg hα (Nat.cast_nonneg _)) hL
  have hscaled :=
    mul_le_mul_of_nonneg_left hchebyshev hscale
  calc
    (((α / (primorial w : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N)) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) =
        (((α / (primorial w : ℝ)) * L) *
          (log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N))) / N := by
      dsimp [L]
      ring
    _ ≤
        (((α / (primorial w : ℝ)) * L) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ)) / N := by
      exact div_le_div_of_nonneg_right hscaled (Nat.cast_nonneg N)
    _ =
        (((α / (primorial w : ℝ)) *
          (#(primesInQuarterInterval
            (wTrickPrimeScale (primorial w) N)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) := by
      dsimp [L]
      ring
    _ ≤ mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) :=
      hmean
