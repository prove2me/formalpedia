-- Prove2me | Theorems.Thm_stageB_dnn
-- name    : stageB_dnn
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T23:54:38.711248+00:00
-- url     : https://prove2.me/theorems/730f6670-c508-4d04-b7be-8ad73d93c856
-- title:
--   stageB_dnn
-- statement:
--   Automatically extracted helper theorem stageB_dnn from oversized parent candidate 5d99a53f41a00b552d4a1668999c9dd8659800e27e8b382ac3e4e1ed0fa1c2dd.
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

theorem stageB_dnn (q : ℝ) (t : WithTop ℝ≥0) : 0 ≤ discountedAt q t := by sorry
