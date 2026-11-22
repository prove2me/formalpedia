-- Prove2me | Theorems.Thm_exists_measTarget_separation
-- name    : exists_measTarget_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:42:04.407836+00:00
-- url     : https://prove2.me/theorems/ba054d12-fe19-4338-9c69-c75f8364e647
-- title:
--   exists meas Target separation: exists meas Target separation
-- statement:
--   Existence form: provided an analytic non-Borel set in ℝ is available, the
--   separation in `analytic_nonborel_set_gives_measTarget_separation` is realised. The
--   unconditional form (with no hypothesis) requires supplying Souslin's classical
--   analytic non-Borel set; this theorem packages the reduction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L360-L364
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L360-L364

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_BorelAnalyticSeparation
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory

theorem exists_measTarget_separation
    (hex : ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget := by sorry
