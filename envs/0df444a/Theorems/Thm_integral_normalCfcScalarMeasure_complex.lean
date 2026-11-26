-- Prove2me | Theorems.Thm_integral_normalCfcScalarMeasure_complex
-- name    : integral_normalCfcScalarMeasure_complex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:03:03.593331+00:00
-- url     : https://prove2.me/theorems/07cc4f26-21e6-4d33-b690-6b9d5ecf10d6
-- title:
--   integral normal Cfc Scalar Measure complex: integral normal Cfc Scalar Measure complex
-- statement:
--   Complex continuous functions have the expected diagonal matrix coefficient against the
--   scalar Riesz measure.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean#L180-L220
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean#L180-L220

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

theorem integral_normalCfcScalarMeasure_complex
    (U : E →L[ℂ] E) (hU : IsStarNormal U) (x : E)
    (f : C(spectrum ℂ U, ℂ)) :
    ∫ z, f z ∂(normalCfcScalarMeasure U hU x) =
      @inner ℂ E _ x ((cfcHom hU) f x) := by sorry
