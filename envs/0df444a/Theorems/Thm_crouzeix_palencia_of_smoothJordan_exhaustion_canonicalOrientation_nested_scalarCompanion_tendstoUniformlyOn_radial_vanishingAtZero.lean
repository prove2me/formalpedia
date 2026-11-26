-- Prove2me | Theorems.Thm_crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:39.262001+00:00
-- url     : https://prove2.me/theorems/05c1df4e-3dbb-4481-b6d4-0d08c7f33b49
-- title:
--   crouzeix palencia of smooth Jordan exhaustion canonical Orientation nested scalar Companion tendsto Uniformly On radial vanishing At Zero: crouzeix palencia of smooth Jordan exhaustion canonical Orien
-- statement:
--   Standard compact-uniform polynomial convergence is sufficient for the
--   canonically oriented nested-exhaustion capstone.  A subsequence realizes the
--   quantitative error schedule required by the preceding theorem.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1108-L1136
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1108-L1136

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

theorem crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_tendstoUniformlyOn_radial_vanishingAtZero
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain) (K : ℕ → Set ℂ)
    (hanti : Antitone K) (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty)
    (hinter : (⋂ n, K n) = closure (numericalRange A))
    (hK : ∀ n, K n = closure (Omega n).carrier)
    (hOmega : ∀ n, closure (numericalRange A) ⊆ (Omega n).carrier)
    (hnest : ∀ n,
      closure (Omega (n + 1)).carrier ⊆ (Omega n).carrier)
    (happrox : ∀ (p : Polynomial ℂ) (n : ℕ), 0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      ∃ q : ℕ → Polynomial ℂ,
        TendstoUniformlyOn
          (fun j z ↦ Polynomial.eval z (q j))
          (crouzeixPolynomialScalarCompanionClosedExtension
            (Omega n).canonicalOrientation p)
          atTop (K n)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
