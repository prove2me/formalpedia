-- Prove2me | Theorems.Thm_normalCfcOperator_unitPole_eq_zero
-- name    : normalCfcOperator_unitPole_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:02:59.178587+00:00
-- url     : https://prove2.me/theorems/a2184e3c-89dd-47e2-b960-bb8b44bb169a
-- title:
--   normal Cfc Operator unit Pole eq zero: normal Cfc Operator unit Pole eq zero
-- statement:
--   The represented normal-CFC projection at the Cayley pole vanishes whenever `1` has no
--   eigenvectors.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean#L1338-L1394
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Existence.lean#L1338-L1394

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

theorem normalCfcOperator_unitPole_eq_zero
    (U : E →L[ℂ] E) (hU : IsStarNormal U)
    (hNoFixed : ∀ x, U x = x → x = 0) :
    normalCfcOperator U hU (unitPole U) = 0 := by sorry
