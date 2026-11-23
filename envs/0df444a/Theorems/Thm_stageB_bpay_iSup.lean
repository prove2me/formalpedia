-- Prove2me | Theorems.Thm_stageB_bpay_iSup
-- name    : stageB_bpay_iSup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T01:03:15.272074+00:00
-- url     : https://prove2.me/theorems/42686235-3ca1-41e1-90ca-c5d3fc0e19f4
-- title:
--   stageB_bpay_iSup
-- statement:
--   Automatically extracted helper theorem stageB_bpay_iSup from oversized parent candidate 8c694b057acd248e08af038d68cb321f7cf2ffcb0fb7618f8d38cc1f8d3d502f.
-- source:
--   candidate-decomposition:47fdba96-7849-46b6-87b0-6cea26c5eadd:8c694b057acd248e08af038d68cb321f7cf2ffcb0fb7618f8d38cc1f8d3d502f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_stageB_Bars
import Definitions.Def_stageB_bpay
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped Classical NNReal ENNReal

theorem stageB_bpay_iSup {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b h q : ℝ) (hb : 0 < b) (hh : 0 < h) (ω : Ω) :
    (⨆ r : stageB_Bars h, stageB_bpay X (r : ℝ) b q ω) =
      if twoSidedExitUpTime X b ω < ⊤ ∧ NoDrawdownBeforeUpcrossing X.X b h ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0 := by sorry
