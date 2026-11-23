-- Prove2me | Theorems.Thm_stageB_actual_height_barrier_semigroup
-- name    : stageB_actual_height_barrier_semigroup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T23:54:32.889101+00:00
-- url     : https://prove2.me/theorems/2525dc26-7524-4bfe-9269-a2ab9c82bb8f
-- title:
--   stageB_actual_height_barrier_semigroup
-- statement:
--   Automatically extracted helper theorem stageB_actual_height_barrier_semigroup from oversized parent candidate 5d99a53f41a00b552d4a1668999c9dd8659800e27e8b382ac3e4e1ed0fa1c2dd.
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

theorem stageB_actual_height_barrier_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∫⁻ ω, if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (b + c) ω).toReal))) else 0 ∂P) =
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal))) else 0 ∂P) *
    (∫⁻ ω, if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal))) else 0 ∂P) := by sorry
