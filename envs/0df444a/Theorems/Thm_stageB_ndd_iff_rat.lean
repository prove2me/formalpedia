-- Prove2me | Theorems.Thm_stageB_ndd_iff_rat
-- name    : stageB_ndd_iff_rat
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T00:50:19.306406+00:00
-- url     : https://prove2.me/theorems/3490a7e9-2eff-4f04-bd90-bb301a416299
-- title:
--   stageB_ndd_iff_rat
-- statement:
--   Automatically extracted helper theorem stageB_ndd_iff_rat from oversized parent candidate 8c694b057acd248e08af038d68cb321f7cf2ffcb0fb7618f8d38cc1f8d3d502f.
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
open scoped NNReal ENNReal

theorem stageB_ndd_iff_rat {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b h : ℝ) (hb : 0 < b) (hh : 0 < h) (ω : Ω)
    (hfin : twoSidedExitUpTime X b ω ≠ ⊤) :
    NoDrawdownBeforeUpcrossing X.X b h ω ↔ ∃ r : stageB_Bars h, stageB_bpay X (r : ℝ) b 0 ω ≠ 0 := by sorry
