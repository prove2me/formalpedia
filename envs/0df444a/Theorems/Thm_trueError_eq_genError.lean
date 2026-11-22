-- Prove2me | Theorems.Thm_trueError_eq_genError
-- name    : trueError_eq_genError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:31.37299+00:00
-- url     : https://prove2.me/theorems/dc8e7df3-f3ca-49cb-bb78-dfcbb367c1f3
-- title:
--   true Error eq gen Error: true Error eq gen Error
-- statement:
--   Bridge: TrueError equals GeneralizationError under 0-1 loss when
--       the disagreement set is measurable.
--       This theorem sits at the HC > 0 joint between ENNReal and ℝ error worlds.
--       KU₁: requires MeasurableSet {x | h x ≠ c x} — which needs [DecidableEq Bool]
--       and measurability of h and c. What are the minimal measurability hypotheses?
--       UK₁: For concept classes where membership is undecidable, this bridge may
--       not have a clean computational witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L179-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L179-L201

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem trueError_eq_genError (X : Type u) [MeasurableSpace X]
    (h : Concept X Bool) (c : Concept X Bool)
    (D : MeasureTheory.Measure X)
    (hmeas : MeasurableSet { x | h x ≠ c x })
    (hcmeas : Measurable c)
    (hhmeas : Measurable h) :
    TrueErrorReal X h c D = GeneralizationError X Bool h
      (D.map (fun x => (x, c x))) (zeroOneLoss Bool) := by sorry
