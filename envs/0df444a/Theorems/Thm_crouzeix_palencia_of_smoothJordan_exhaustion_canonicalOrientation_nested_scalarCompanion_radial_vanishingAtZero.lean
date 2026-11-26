-- Prove2me | Theorems.Thm_crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero
-- name    : crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:04.847732+00:00
-- url     : https://prove2.me/theorems/7ff76b25-1d85-4bbc-bbc0-c3ede79cbf62
-- title:
--   crouzeix palencia of smooth Jordan exhaustion canonical Orientation nested scalar Companion radial vanishing At Zero: crouzeix palencia of smooth Jordan exhaustion canonical Orientation nested scalar
-- statement:
--   Canonical orientation removes the numerical-range support premise from
--   the general strictly nested smooth-exhaustion assembly as well.  This version
--   does not require the carriers to be particular metric thickenings: compact
--   exhaustion, numerical-range containment, strict adjacent nesting, and uniform
--   approximation of the canonically oriented closed companions suffice.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1061-L1103
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1061-L1103

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

theorem crouzeix_palencia_of_smoothJordan_exhaustion_canonicalOrientation_nested_scalarCompanion_radial_vanishingAtZero
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
      ∃ r : ℕ → Polynomial ℂ,
        ∀ (j : ℕ) (z : ℂ), z ∈ K n →
          ‖Polynomial.eval z (r j) -
            crouzeixPolynomialScalarCompanionClosedExtension
              (Omega n).canonicalOrientation p z‖ ≤
            1 / ((j : ℝ) + 1)) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
