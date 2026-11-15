-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.normalizer_pos
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:59:34.915352+00:00
-- url     : https://prove2.me/submissions/18256c57-e2e3-4943-8b6a-19199c2c508e

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section







/-!
# Smooth sieve cutoffs

This file packages the smooth cutoff used by the Goldston--Yıldırım
divisor sum.  It also constructs a concrete cutoff from Mathlib's smooth
bump-function infrastructure and proves that its derivative-square
normalizer is positive.
-/

namespace Wikipedia.SzemeredisTheorem

open Function Set MeasureTheory
open scoped ContDiff



namespace SmoothSieveCutoff















/-- The derivative-square integrand is continuous. -/
theorem continuous_deriv_sq (χ : SmoothSieveCutoff) :
    Continuous (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2) := by
  exact (χ.smooth.continuous_deriv (by simp)).abs.pow 2

/-- The derivative-square integrand also has compact support. -/
theorem hasCompactSupport_deriv_sq (χ : SmoothSieveCutoff) :
    HasCompactSupport (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-1) 1) isCompact_Icc
  have htsupport :
      tsupport χ.toFun ⊆ Set.Icc (-1) 1 :=
    closure_minimal χ.support_subset isClosed_Icc
  intro x hx
  apply htsupport
  apply support_deriv_subset
  intro hderiv
  apply hx
  simp [hderiv]



end SmoothSieveCutoff











end Wikipedia.SzemeredisTheorem

end
/-!
# Smooth sieve cutoffs

This file packages the smooth cutoff used by the Goldston--Yıldırım
divisor sum.  It also constructs a concrete cutoff from Mathlib's smooth
bump-function infrastructure and proves that its derivative-square
normalizer is positive.
-/
open Wikipedia.SzemeredisTheorem
open Function Set MeasureTheory
open scoped ContDiff
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Every object satisfying the cutoff axioms has positive derivative
energy: it changes from `1` at zero to `0` at one. -/
theorem solution (χ : SmoothSieveCutoff) :
    0 < χ.normalizer := by
  have hcont :
      ContinuousOn χ.toFun (Set.Icc (0 : ℝ) 1) :=
    χ.smooth.continuous.continuousOn
  have hdiff :
      DifferentiableOn ℝ χ.toFun (Set.Ioo (0 : ℝ) 1) :=
    (χ.smooth.differentiable (by simp)).differentiableOn
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope χ.toFun
      (by norm_num : (0 : ℝ) < 1) hcont hdiff
  have hcderiv_ne : deriv χ.toFun c ≠ 0 := by
    rw [hcderiv, χ.zero_of_one_le 1 le_rfl, χ.value_zero]
    norm_num
  have henergy_cont :
      Continuous (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2) :=
    χ.continuous_deriv_sq
  have henergy_int :
      IntegrableOn (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2)
        (Set.Ioi (0 : ℝ)) :=
    (henergy_cont.integrable_of_hasCompactSupport
      χ.hasCompactSupport_deriv_sq).integrableOn
  have henergy_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun x : ℝ ↦ |deriv χ.toFun x| ^ 2) :=
    Filter.Eventually.of_forall fun x ↦ sq_nonneg _
  rw [normalizer]
  apply
    (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      henergy_nonneg henergy_int).2
  apply
    (henergy_cont.isOpen_support.inter isOpen_Ioi).measure_pos volume
  exact
    ⟨c, pow_ne_zero 2 (abs_ne_zero.mpr hcderiv_ne), hc.1⟩
