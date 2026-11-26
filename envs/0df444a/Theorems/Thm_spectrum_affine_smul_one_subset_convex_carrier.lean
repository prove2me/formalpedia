-- Prove2me | Theorems.Thm_spectrum_affine_smul_one_subset_convex_carrier
-- name    : spectrum_affine_smul_one_subset_convex_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:53.547137+00:00
-- url     : https://prove2.me/theorems/05000986-9958-4fa0-aed3-77c773e433a7
-- title:
--   spectrum affine smul one subset convex carrier: spectrum affine smul one subset convex carrier
-- statement:
--   The spectrum affine smul one subset convex carrier construction uses the spectrum affine smul one subset convex carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L343-L374
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L343-L374

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem spectrum_affine_smul_one_subset_convex_carrier
    [Nontrivial E] (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    spectrum ℂ (c • (1 : E →L[ℂ] E) +
      (r : ℂ) • (A - c • (1 : E →L[ℂ] E))) ⊆ Omega.carrier := by sorry
