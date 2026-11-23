-- Prove2me | Theorems.Thm_stageB_tauPlus_lt_iff
-- name    : stageB_tauPlus_lt_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T00:43:52.985811+00:00
-- url     : https://prove2.me/theorems/770b697b-7019-4a34-a2c1-fb29f294ecbb
-- title:
--   stageB_tauPlus_lt_iff
-- statement:
--   Automatically extracted helper theorem stageB_tauPlus_lt_iff from oversized parent candidate 8c694b057acd248e08af038d68cb321f7cf2ffcb0fb7618f8d38cc1f8d3d502f.
-- source:
--   candidate-decomposition:47fdba96-7849-46b6-87b0-6cea26c5eadd:8c694b057acd248e08af038d68cb321f7cf2ffcb0fb7618f8d38cc1f8d3d502f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem stageB_tauPlus_lt_iff {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) {t : ℝ≥0} :
    (t : WithTop ℝ≥0) < tauPlus X.X a ω ↔ (t : ℝ≥0∞) < twoSidedExitUpTime X a ω := by sorry
