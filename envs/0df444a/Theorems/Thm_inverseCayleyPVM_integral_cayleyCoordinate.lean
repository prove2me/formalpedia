-- Prove2me | Theorems.Thm_inverseCayleyPVM_integral_cayleyCoordinate
-- name    : inverseCayleyPVM_integral_cayleyCoordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:02:46.4838+00:00
-- url     : https://prove2.me/theorems/c878dd02-47c5-5caf-ba8b-0d6939def50d
-- title:
--   inverse Cayley PVM integral cayley Coordinate: inverse Cayley PVM integral cayley Coordinate
-- statement:
--   Integrating the scalar Cayley coordinate against the inverse-Cayley PVM recovers the
--   unitary operator.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean#L1535-L1580
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean#L1535-L1580

import Definitions.Def_Spectral_Cayley_Inverse
import Definitions.Def_Spectral_PVM_Unbounded
import Definitions.Def_Spectral_Spectral_CayleyCalculus
import Definitions.Def_Spectral_Spectral_Polarization
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Spectral_Spectral_Existence
set_option autoImplicit false
open MeasureTheory
open CompactlySupported
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem inverseCayleyPVM_integral_cayleyCoordinate
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hunit : U ∈ unitary (E →L[ℂ] E))
    (hNoFixed : ∀ x, U x = x → x = 0) :
    (inverseCayleyPVM U hU).integral cayleyCoordinate
      cayleyCoordinate_measurable cayleyCoordinate_bounded = U := by sorry
