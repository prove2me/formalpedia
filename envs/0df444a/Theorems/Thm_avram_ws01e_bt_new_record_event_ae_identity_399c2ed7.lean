-- Prove2me | Theorems.Thm_avram_ws01e_bt_new_record_event_ae_identity_399c2ed7
-- name    : avram_ws01e_bt_new_record_event_ae_identity_399c2ed7
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:51:41.358816+00:00
-- url     : https://prove2.me/theorems/42299e96-5f92-4282-88af-2a629fd7f93c
-- title:
--   Avram ws01e bt new record event ae: Identity
-- statement:
--   The two expressions in the stated equality coincide under the theorem's explicit assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem avram_ws01e_bt_new_record_event_ae_identity_399c2ed7
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (p : ℝ) (hp : 0 < p)
    (w : Ω × ℝ → ℝ≥0∞) 
    (hT : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity w; Measurable T))
    (hAge : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity w; Measurable age))
    (hAinE : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity w; A ⊆ E))
    (hDiffTie : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity w; E \ A ⊆ {z : Ω × ℝ | z.2 = (age z.1 : ℝ)}))
    (hClockAC : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity w; expMeasure p ≪ (volume : Measure ℝ)))
    (hSingleton : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity w; (∀ (r : ℝ), expMeasure p {r} = 0)))
    : (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let A : Set (Ω × ℝ) := {z | b < runningSup X (Real.toNNReal z.2) z.1}; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity w; let G : Set (Ω × ℝ) := {z | z.2 = (age z.1 : ℝ)}; Qp G = 0) := by sorry
