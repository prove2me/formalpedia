-- Prove2me | Theorems.Thm_analytic_nonborel_set_gives_measTarget_separation
-- name    : analytic_nonborel_set_gives_measTarget_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:37.625382+00:00
-- url     : https://prove2.me/theorems/dffd8170-4063-4c3a-8902-ecd79ba6529d
-- title:
--   analytic nonborel set gives meas Target separation: analytic nonborel set gives meas Target separation
-- statement:
--   **Main separation theorem.** Given any analytic non-Borel set `A ⊆ ℝ`, the
--   concept class obtained by parameterising `singletonConcept` (plus `zeroConcept`) over
--   `A` is a concrete witness that `WellBehavedVCMeasTarget` is strictly weaker than the
--   Krapp-Wirth Borel condition. The class is constructed as `Set.range e` for an
--   evaluation map `e : Bool × β → Concept ℝ Bool` built from a Polish parameterisation of
--   `A`; post-construction, `Set.range e` equals `singletonClassOn (Set.range g)` where `g`
--   realises `A`.
--
--   The class satisfies:
--
--   * `MeasurableHypotheses`: every individual hypothesis is Borel
--     (`singletonClassOn_measurable`).
--   * `WellBehavedVCMeasTarget`: the bad event is analytic
--     (`planarWitnessEvent_analytic` lifted via `singleton_badEvent_eq_preimage_planar`),
--     hence `NullMeasurableSet` by the Choquet bridge.
--   * NOT `KrappWirthWellBehaved`: the bad event is not Borel
--     (`singleton_badEvent_not_measurable`).
--
--   The separation is realised by passing through the standard Borel space ℝ as the
--   parameter space; the construction reuses no problem-specific fact beyond the existence
--   of an analytic non-Borel subset of ℝ (Souslin's classical result), supplied in
--   `exists_measTarget_separation`. The witness shows that the measurable-target variant
--   proved in this kernel is a genuine improvement over the existing literature, not a
--   restatement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L242-L354
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/BorelAnalyticSeparation.lean#L242-L354

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

theorem analytic_nonborel_set_gives_measTarget_separation
    (A : Set ℝ)
    (hA_an : MeasureTheory.AnalyticSet A)
    (hA_non : ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget := by sorry
