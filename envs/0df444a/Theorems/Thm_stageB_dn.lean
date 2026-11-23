-- Prove2me | Theorems.Thm_stageB_dn
-- name    : stageB_dn
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T23:54:44.114486+00:00
-- url     : https://prove2.me/theorems/2394d9d3-d582-49b6-9093-ebd0ef361a06
-- title:
--   stageB_dn
-- statement:
--   Automatically extracted helper theorem stageB_dn from oversized parent candidate 5d99a53f41a00b552d4a1668999c9dd8659800e27e8b382ac3e4e1ed0fa1c2dd.
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

theorem stageB_dn (q : ℝ) (hq : 0 ≤ q) (t : WithTop ℝ≥0) : ‖discountedAt q t‖ ≤ 1 := by sorry
