-- Prove2me | Theorems.Thm_vcdim_bounds_rademacher_quantitative
-- name    : vcdim_bounds_rademacher_quantitative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:35:17.795667+00:00
-- url     : https://prove2.me/theorems/e582237a-103a-4937-825f-1c690e719162
-- title:
--   vcdim bounds rademacher quantitative: vcdim bounds rademacher quantitative
-- statement:
--   VC dimension upper bounds Rademacher complexity: Rad ≤ √(2d·log(em/d)/m).
--
--       The proof decomposes into:
--       (1) Pointwise: EmpRad(xs) ≤ B for all xs [Massart + Sauer-Shelah]
--       (2) Integral: Rad = ∫ EmpRad ≤ ∫ B = B [probability measure]
--
--       Step (2) is proved. Step (1) for B ≥ 1 follows from EmpRad ≤ 1.
--       Step (1) for B < 1 requires Massart finite lemma + Sauer-Shelah growth bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L838-L1069
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Rademacher.lean#L838-L1069

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem vcdim_bounds_rademacher_quantitative (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) (hm : 0 < m)
    (d : ℕ) (hd : VCDim X C = ↑d) (hd_pos : 0 < d) (hdm : d ≤ m)
    [MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ Real.sqrt (2 * d * Real.log (Real.exp 1 * ↑m / d) / m) := by sorry
