-- Prove2me | Theorems.Thm_pac_bayes_per_hypothesis
-- name    : pac_bayes_per_hypothesis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:37:33.305794+00:00
-- url     : https://prove2.me/theorems/635f8a82-5c11-44f7-a6c8-bd8135019b36
-- title:
--   pac bayes per hypothesis: pac bayes per hypothesis
-- statement:
--   Per-hypothesis Hoeffding with prior-weighted tail.
--       For each h with prior weight P(h), the probability that
--       TrueErr(h) exceeds EmpErr(h,S) + √(log(1/(P(h)·δ))/(2m))
--       is at most P(h)·δ.
--
--       This is Hoeffding's inequality with t = √(log(1/(P(h)·δ))/(2m)).
--
--       We require the bound parameter t ≤ 1 for Hoeffding's applicability.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PACBayes.lean#L74-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PACBayes.lean#L74-L168

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

theorem pac_bayes_per_hypothesis {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h₀ : H)
    (hbound_le_one : Real.sqrt (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m)) ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        TrueErrorReal X (hs h₀) c D >
          EmpiricalError X Bool (hs h₀) (fun i => (S i, c (S i))) (zeroOneLoss Bool) +
          Real.sqrt (Real.log (1 / (P.prob h₀ * δ)) / (2 * ↑m)) }
      ≤ ENNReal.ofReal (P.prob h₀ * δ) := by sorry
