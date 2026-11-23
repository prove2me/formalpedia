-- Prove2me | Theorems.Thm_stageB_reflect_eq
-- name    : stageB_reflect_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:54:35.595039+00:00
-- url     : https://prove2.me/theorems/243cbdfd-4c9f-4583-b199-252bfc777d79
-- title:
--   stageB_reflect_eq
-- statement:
--   Automatically extracted helper theorem stageB_reflect_eq from oversized parent candidate 5d99a53f41a00b552d4a1668999c9dd8659800e27e8b382ac3e4e1ed0fa1c2dd.
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

theorem stageB_reflect_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (ω : Ω) : reflectAtSup X.X 0 t ω = reflectedSup X t ω := by sorry
