-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_threshold_cutoffZetaSystemFactor_close
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:52:11.983342+00:00
-- url     : https://prove2.me/submissions/b2ee54e6-d3ba-4ec2-acbe-eca658e73f08

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cutoffZetaSystemFactor_close_on_box
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_fourierZetaBoxRadius_real

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









/-! ## The standard growing truncation box -/



theorem tendsto_fourierZetaBoxRadius_nat :
    Tendsto
      (fun R : ℕ =>
        (1 + 2 * Real.pi *
            Real.sqrt (Real.log R)) /
          Real.log R)
      atTop (𝓝 0) := by
  exact tendsto_fourierZetaBoxRadius_real.comp
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)



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
/-! ## The standard growing truncation box -/

open Wikipedia.SzemeredisTheorem in
/-- On the conventional truncation region
`|t_i|, |u_i| ≤ sqrt (log R)`, the completed finite zeta factor is uniformly
close to one for all sufficiently large `R`. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ,
      ∀ R, R₀ ≤ R →
      ∀ (t u : κ → ℝ),
        (∀ i, |t i| ≤ Real.sqrt (Real.log R)) →
        (∀ i, |u i| ≤ Real.sqrt (Real.log R)) →
        ‖cutoffZetaSystemFactor R t u - 1‖ < ε := by
  obtain ⟨δ, hδ, hbox⟩ :=
    exists_cutoffZetaSystemFactor_close_on_box
      (κ := κ) hε
  have hlarge :
      ∀ᶠ R : ℕ in atTop, 1 < R :=
    eventually_gt_atTop 1
  have hdist :
      ∀ᶠ R : ℕ in atTop,
        dist
          ((1 + 2 * Real.pi *
              Real.sqrt (Real.log R)) /
            Real.log R)
          0 < δ :=
    Metric.tendsto_nhds.mp
      tendsto_fourierZetaBoxRadius_nat δ hδ
  have hsmall :
      ∀ᶠ R : ℕ in atTop,
        (1 + 2 * Real.pi *
            Real.sqrt (Real.log R)) /
          Real.log R < δ := by
    filter_upwards [hdist, hlarge] with R hdistR hR
    have hlog :
        0 < Real.log (R : ℝ) :=
      Real.log_pos (by exact_mod_cast hR)
    have hnum :
        0 ≤
          1 + 2 * Real.pi *
            Real.sqrt (Real.log R) := by
      positivity
    have hfrac :
        0 ≤
          (1 + 2 * Real.pi *
              Real.sqrt (Real.log R)) /
            Real.log R :=
      div_nonneg hnum hlog.le
    have habs :
        |(1 + 2 * Real.pi *
              Real.sqrt (Real.log R)) /
            Real.log R| < δ := by
      simpa only [Real.dist_eq, sub_zero] using hdistR
    rw [abs_of_nonneg hfrac] at habs
    exact habs
  rw [eventually_atTop] at hsmall hlarge
  obtain ⟨R₁, hR₁⟩ := hsmall
  obtain ⟨R₂, hR₂⟩ := hlarge
  refine ⟨max R₁ R₂, fun R hR t u ht hu => ?_⟩
  exact hbox (hR₂ R ((le_max_right R₁ R₂).trans hR))
    t u
    (hR₁ R ((le_max_left R₁ R₂).trans hR))
    ht hu
