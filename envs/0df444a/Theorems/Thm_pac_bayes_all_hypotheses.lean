-- Prove2me | Theorems.Thm_pac_bayes_all_hypotheses
-- name    : pac_bayes_all_hypotheses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:44.033837+00:00
-- url     : https://prove2.me/theorems/7d1855d2-f97e-4b86-8e98-333bc98e73a2
-- title:
--   pac bayes all hypotheses: pac bayes all hypotheses
-- statement:
--   Simultaneous PAC-Bayes bound: with probability ≥ 1-δ,
--       ALL hypotheses h simultaneously satisfy
--       TrueErr(h) ≤ EmpErr(h,S) + √(log(1/(P(h)·δ))/(2m)).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PACBayes.lean#L190-L277
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PACBayes.lean#L190-L277

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PACBayes
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Finset

theorem pac_bayes_all_hypotheses {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        ∀ h : H,
          TrueErrorReal X (hs h) c D ≤
            EmpiricalError X Bool (hs h) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
            Real.sqrt (Real.log (1 / (P.prob h * δ)) / (2 * ↑m)) }
      ≥ ENNReal.ofReal (1 - δ) := by sorry
