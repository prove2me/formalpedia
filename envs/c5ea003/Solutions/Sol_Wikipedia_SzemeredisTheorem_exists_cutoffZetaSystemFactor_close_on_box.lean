-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_cutoffZetaSystemFactor_close_on_box
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:51:26.854198+00:00
-- url     : https://prove2.me/submissions/1bd630f6-bf4b-48fc-b13f-a2b465ff70cf

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_norm_normalizedZetaSystemFactor_sub_one_lt
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_cutoffZetaShift_le_of_abs_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Fourier parameters for the zeta comparison

`SmoothCutoffFourier` fixes Mathlib's analyst normalization.  Its divisor
phase is

`exp (-x + 2 π i t x)`, where `x = log d / log R`.

Thus the exact complex shift occurring in the Euler and zeta factors is

`(1 - 2 π i t) / log R`.

This file records that conversion, its positivity and elementary norm
bounds, and the resulting access to the completed zeta estimates.  Keeping
this bridge explicit prevents a hidden `2π` or sign error when the
multivariate Fourier integral is assembled.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology





















/-! ## Finite Fourier systems -/





/-- Uniform finite-system zeta comparison, stated directly for the exact
Fourier shifts. -/
theorem exists_norm_cutoffZetaSystemFactor_sub_one_lt
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (R : ℕ) (t u : κ → ℝ),
        (∀ i, ‖cutoffZetaShift R (t i)‖ < δ) →
        (∀ i, ‖cutoffZetaShift R (u i)‖ < δ) →
        ‖cutoffZetaSystemFactor R t u - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    exists_norm_normalizedZetaSystemFactor_sub_one_lt
      (κ := κ) hε
  refine ⟨δ, hδ, fun R t u ht hu => ?_⟩
  rw [cutoffZetaSystemFactor]
  apply hclose
  · exact (pi_norm_lt_iff hδ).2 ht
  · exact (pi_norm_lt_iff hδ).2 hu



/-! ## The standard growing truncation box -/







end Wikipedia.SzemeredisTheorem

end
/-!
# Fourier parameters for the zeta comparison

`SmoothCutoffFourier` fixes Mathlib's analyst normalization.  Its divisor
phase is

`exp (-x + 2 π i t x)`, where `x = log d / log R`.

Thus the exact complex shift occurring in the Euler and zeta factors is

`(1 - 2 π i t) / log R`.

This file records that conversion, its positivity and elementary norm
bounds, and the resulting access to the completed zeta estimates.  Keeping
this bridge explicit prevents a hidden `2π` or sign error when the
multivariate Fourier integral is assembled.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## Finite Fourier systems -/

open Wikipedia.SzemeredisTheorem in
/-- Ready-to-use zeta comparison on a common truncated Fourier box.  All
analytic smallness is reduced to the displayed scalar inequality. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {R : ℕ}, 1 < R →
      ∀ {T : ℝ} (t u : κ → ℝ),
        (1 + 2 * Real.pi * T) /
            Real.log R < δ →
        (∀ i, |t i| ≤ T) →
        (∀ i, |u i| ≤ T) →
        ‖cutoffZetaSystemFactor R t u - 1‖ < ε := by
  obtain ⟨δ, hδ, hclose⟩ :=
    exists_norm_cutoffZetaSystemFactor_sub_one_lt
      (κ := κ) hε
  refine ⟨δ, hδ, ?_⟩
  intro R hR T t u hsmall ht hu
  exact hclose R t u
    (fun i =>
      (norm_cutoffZetaShift_le_of_abs_le
        hR (ht i)).trans_lt hsmall)
    (fun i =>
      (norm_cutoffZetaShift_le_of_abs_le
        hR (hu i)).trans_lt hsmall)
