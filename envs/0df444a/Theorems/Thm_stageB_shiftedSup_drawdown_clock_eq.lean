-- Prove2me | Theorems.Thm_stageB_shiftedSup_drawdown_clock_eq
-- name    : stageB_shiftedSup_drawdown_clock_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T00:16:17.469412+00:00
-- url     : https://prove2.me/theorems/05410d73-91b9-4cec-a116-08f52724819d
-- title:
--   stageB shifted drawdown clock equality
-- statement:
--   Source-faithful helper theorem isolating the shifted drawdown-clock equality used by the actual-height barrier semigroup: the first time a shifted increment falls below -a below its running supremum equals the first time the shifted path falls below -a below its unshifted running supremum.
-- source:
--   candidate-decomposition:47fdba96-7849-46b6-87b0-6cea26c5eadd:8c694b057acd248e08af038d68cb321f7cf2ffcb0fb7618f8d3d502f:manual-complexity-split

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_filtered_avram_model
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_killed_future_reward_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_fresh_reflected_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_origin_sampled_reflected_reward_eq_true
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_shifted_sampled_reward_true_pair
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_two_record_discount_pathwise
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_strictly_before_drawdown_ruin
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Theorems.Thm_AvramDividend_Classical_upperPassage_measurable_from_stopping
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem stageB_shiftedSup_drawdown_clock_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) (u : ℝ≥0) :
    (⨅ i : {t : ℝ≥0 // (X.X (u + t) ω - X.X u ω) -
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) '' Icc 0 t) < -a},
      (i.1 : ℝ≥0∞)) =
    (⨅ i : {t : ℝ≥0 // X.X (u + t) ω -
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a},
      (i.1 : ℝ≥0∞)) := by sorry
