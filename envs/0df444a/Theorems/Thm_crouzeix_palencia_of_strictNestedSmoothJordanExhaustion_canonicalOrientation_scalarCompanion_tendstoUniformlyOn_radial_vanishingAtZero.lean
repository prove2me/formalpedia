-- Prove2me | Theorems.Thm_crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:49.682687+00:00
-- url     : https://prove2.me/theorems/347d0256-74f9-5528-92f9-d90da3559e70
-- title:
--   crouzeix palencia of strict Nested Smooth Jordan Exhaustion canonical Orientation scalar Companion tendsto Uniformly On radial vanishing At Zero: crouzeix palencia of strict Nested Smooth Jordan Exhau
-- statement:
--   Terminal bundled form of the verified Crouzeix--Palencia assembly.  A
--   strictly nested smooth Jordan exhaustion of the closed numerical range and
--   compact-uniform polynomial approximation of its canonically oriented closed
--   scalar companions imply the exact `1 + sqrt 2` spectral-set bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1142-L1169
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1142-L1169

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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
    (A : E →L[ℂ] E)
    (Omega : StrictNestedSmoothJordanExhaustion
      (closure (numericalRange A)))
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ q : ℕ → Polynomial ℂ,
        TendstoUniformlyOn
          (fun j z ↦ Polynomial.eval z (q j))
          (crouzeixPolynomialScalarCompanionClosedExtension
            (Omega.domain n).canonicalOrientation p)
          atTop (closure (Omega.domain n).carrier)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
