-- Prove2me | Theorems.Thm_not_KrappWirth_of_nonBorel_badEvent
-- name    : not_KrappWirth_of_nonBorel_badEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:13.880323+00:00
-- url     : https://prove2.me/theorems/927d4fff-cdd8-4421-89b5-c7dda5bff530
-- title:
--   not Krapp Wirth of non Borel bad Event: not Krapp Wirth of non Borel bad Event
-- statement:
--   If the one-sided ghost gap bad event is NOT MeasurableSet,
--       then KrappWirthWellBehaved fails. Measurability can only descend.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L181-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Interpolation.lean#L181-L192

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_BorelAnalyticBridge
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Interpolation
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem not_KrappWirth_of_nonBorel_badEvent
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ)
    (hC : C.Nonempty)
    (hbad : ¬ MeasurableSet {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
      oneSidedGhostGap h c m p ≥ ε / 2}) :
    ¬ KrappWirthWellBehaved X C := by sorry
