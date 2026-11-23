-- Prove2me | Theorems.Thm_stageB_tauPlus_coe_eq
-- name    : stageB_tauPlus_coe_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:54:32.76645+00:00
-- url     : https://prove2.me/theorems/3488bc05-f015-4d64-a570-28f0921c1456
-- title:
--   stageB_tauPlus_coe_eq
-- statement:
--   Automatically extracted helper theorem stageB_tauPlus_coe_eq from oversized parent candidate 5d99a53f41a00b552d4a1668999c9dd8659800e27e8b382ac3e4e1ed0fa1c2dd.
-- source:
--   candidate-decomposition:47fdba96-7849-46b6-87b0-6cea26c5eadd:5d99a53f41a00b552d4a1668999c9dd8659800e27e8b382ac3e4e1ed0fa1c2dd

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem stageB_tauPlus_coe_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) : (tauPlus X.X a ω : ℝ≥0∞) = twoSidedExitUpTime X a ω := by sorry
