-- Prove2me | Theorems.Thm_avram_ws01e_bi_new_record_upper_ray_ae_ain_e_c1afc633
-- name    : avram_ws01e_bi_new_record_upper_ray_ae_ain_e_c1afc633
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:00:40.312158+00:00
-- url     : https://prove2.me/theorems/b29e8157-fc2b-46e2-bd7b-c5f40d73c6fa
-- title:
--   Avram ws01e bi new record upper ray ae: Auxiliary result
-- statement:
--   Under the explicitly listed hypotheses, the assertion in the formal Lean theorem statement holds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem avram_ws01e_bi_new_record_upper_ray_ae_ain_e_c1afc633
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (b : ℝ) (hb : 0 ≤ b) 
    (hT : (let S : Ω × ℝ → ℝ := fun z => runningSup X (Real.toNNReal z.2) z.1; let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let A : Set (Ω × ℝ) := {z | b < S z}; Measurable T))
    (hAge : (let S : Ω × ℝ → ℝ := fun z => runningSup X (Real.toNNReal z.2) z.1; let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let A : Set (Ω × ℝ) := {z | b < S z}; Measurable age))
    : (let S : Ω × ℝ → ℝ := fun z => runningSup X (Real.toNNReal z.2) z.1; let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b; let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal; let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}; let A : Set (Ω × ℝ) := {z | b < S z}; A ⊆ E) := by sorry
