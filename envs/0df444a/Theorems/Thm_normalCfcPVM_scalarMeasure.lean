-- Prove2me | Theorems.Thm_normalCfcPVM_scalarMeasure
-- name    : normalCfcPVM_scalarMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:02:48.892748+00:00
-- url     : https://prove2.me/theorems/e16be4d3-a9d8-502d-b7c7-9fa000ea1834
-- title:
--   normal Cfc PVM scalar Measure: normal Cfc PVM scalar Measure
-- statement:
--   Scalar measures of a pulled-back normal CFC resolution are pushforwards of its Riesz
--   measures.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean#L1290-L1301
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean#L1290-L1301

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

theorem normalCfcPVM_scalarMeasure
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (g : spectrum ℂ U → ℝ) (hg : Measurable g) (x : E) :
    (normalCfcPVM U hU g hg).scalarMeasure x =
      Measure.map g (normalCfcScalarMeasure U hU x) := by sorry
