-- Prove2me | Theorems.Thm_pac_bayes_finite
-- name    : pac_bayes_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:42:23.885198+00:00
-- url     : https://prove2.me/theorems/b10a99cb-04c6-4cec-9cc1-3b2e27fddc83
-- title:
--   pac bayes finite: pac bayes finite
-- statement:
--   McAllester's PAC-Bayes bound (finite hypothesis class, union-bound version).
--
--       With probability ≥ 1-δ over the sample S of size m, for ALL posteriors Q:
--
--         E_{h~Q}[TrueErr(h)] ≤ E_{h~Q}[EmpErr(h,S)]
--           + √((crossEntropyFinitePMF Q P + log(1/δ)) / (2m))
--
--       where crossEntropyFinitePMF Q P = ∑_h Q(h)·log(1/P(h)) = KL(Q‖P) + H(Q).
--
--       This is the union-bound version. The tight change-of-measure version
--       replaces crossEntropyFinitePMF with klDivFinitePMF and adds log(m).
--
--       The tighter change-of-measure version (Catoni 2007) is not included here:
--         E_Q[TrueErr] ≤ E_Q[EmpErr] + √((KL(Q‖P) + log(2√m/δ))/(2m))
--
--       Reference: McAllester, COLT 1999.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PACBayes.lean#L416-L448
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PACBayes.lean#L416-L448

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

theorem pac_bayes_finite {X : Type u} [MeasurableSpace X]
    {H : Type*} [Fintype H]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (hs : H → Concept X Bool) (hhs_meas : ∀ h, Measurable (hs h))
    (P : FinitePMF H) (hP_pos : ∀ h, 0 < P.prob h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { S : Fin m → X |
        ∀ (Q : FinitePMF H),
          gibbsError Q hs c D ≤
            gibbsEmpError Q hs c S +
            Real.sqrt ((crossEntropyFinitePMF Q P + Real.log (1 / δ)) / (2 * ↑m)) }
      ≥ ENNReal.ofReal (1 - δ) := by sorry
