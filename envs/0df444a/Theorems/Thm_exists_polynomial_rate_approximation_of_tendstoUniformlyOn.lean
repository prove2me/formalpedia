-- Prove2me | Theorems.Thm_exists_polynomial_rate_approximation_of_tendstoUniformlyOn
-- name    : exists_polynomial_rate_approximation_of_tendstoUniformlyOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:18.925569+00:00
-- url     : https://prove2.me/theorems/94ecbb96-99f6-4dfe-a75f-04eb5a564acf
-- title:
--   exists polynomial rate approximation of tendsto Uniformly On: exists polynomial rate approximation of tendsto Uniformly On
-- statement:
--   A uniformly convergent polynomial sequence has a subsequence with the
--   explicit error schedule `1, 1/2, 1/3, ...`.  This converts the standard output
--   of a polynomial approximation theorem into the quantitative interface used by
--   the exhaustion assembly.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L24-L42
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L24-L42

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real

theorem exists_polynomial_rate_approximation_of_tendstoUniformlyOn
    (K : Set ℂ) (f : ℂ → ℂ) (q : ℕ → Polynomial ℂ)
    (hlim : TendstoUniformlyOn
      (fun j z ↦ Polynomial.eval z (q j)) f atTop K) :
    ∃ r : ℕ → Polynomial ℂ,
      ∀ (j : ℕ) (z : ℂ), z ∈ K →
        ‖Polynomial.eval z (r j) - f z‖ ≤ 1 / ((j : ℝ) + 1) := by sorry
