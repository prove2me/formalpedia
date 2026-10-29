-- Prove2me | Theorems.Thm_avram_ws01e_bt_new_record_event_ae_ain_e_fce9933b
-- name    : avram_ws01e_bt_new_record_event_ae_ain_e_fce9933b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:51:18.598762+00:00
-- url     : https://prove2.me/theorems/1edc349e-2e83-434e-bbaf-76541e552f44
-- title:
--   Avram ws01e bt new record event ae: Auxiliary result
-- statement:
--   Under the explicitly listed hypotheses, the assertion in the formal Lean theorem statement holds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem avram_ws01e_bt_new_record_event_ae_ain_e_fce9933b
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (p : ℝ) (hp : 0 < p)
    (w : Ω × ℝ → ℝ≥0∞) 
    (hT : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; Measurable T))
    (hAge : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; Measurable age))
    : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; A ⊆ E) := by sorry
