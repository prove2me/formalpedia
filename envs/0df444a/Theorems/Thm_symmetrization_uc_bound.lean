-- Prove2me | Theorems.Thm_symmetrization_uc_bound
-- name    : symmetrization_uc_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:39.020674+00:00
-- url     : https://prove2.me/theorems/68b95b62-5cec-4a7c-b840-eeeb5ad1e8f1
-- title:
--   symmetrization uc bound: symmetrization uc bound
-- statement:
--   The symmetrization uniform convergence bound: two-sided version.
--       P[∃h∈C: |TrueErr-EmpErr| ≥ ε] ≤ 4·GF(C,2m)·exp(-mε²/8).
--
--       **Proof strategy (4 steps):**
--
--       1. **Decompose absolute value:**
--          |TrueErr - EmpErr| ≥ ε ↔ (TrueErr - EmpErr ≥ ε) ∨ (EmpErr - TrueErr ≥ ε)
--
--          ```
--          have abs_decomp : ∀ (a b : ℝ),
--            |a - b| ≥ ε ↔ a - b ≥ ε ∨ b - a ≥ ε := by
--            intro a b; constructor
--            · intro h; by_cases h' : a - b ≥ ε
--              · exact Or.inl h'
--              · exact Or.inr (by linarith [abs_sub_comm a b, le_abs_self (a - b)])
--            · intro h; cases h with
--              | inl h => exact le_trans (le_of_eq (abs_of_nonneg (by linarith))) (by linarith)
--              | inr h => exact le_trans (le_of_eq (abs_of_nonpos (by linarith) ▸ ...)) ...
--          ```
--
--       2. **Upper tail:** P[∃h∈C: TrueErr-EmpErr ≥ ε] ≤ 2·GF(C,2m)·exp(-mε²/8)
--          - Direct application of `symmetrization_step` + `double_sample_pattern_bound`.
--
--       3. **Lower tail:** P[∃h∈C: EmpErr-TrueErr ≥ ε] ≤ 2·GF(C,2m)·exp(-mε²/8)
--          - Apply the symmetric argument: swap roles of S and S' in the double sample.
--          - Equivalently, apply `symmetrization_step` to the event EmpErr-TrueErr ≥ ε
--            and bound the double-sample event {EmpErr_S - EmpErr_{S'} ≥ ε/2}.
--          - The bound is symmetric because D^m ⊗ D^m is symmetric under swapping factors.
--          ```
--          have swap_symmetry :
--            DoubleSampleMeasure D m {p | ∃ h ∈ C, EmpErr(S) - EmpErr(S') ≥ ε/2}
--            = DoubleSampleMeasure D m {p | ∃ h ∈ C, EmpErr(S') - EmpErr(S) ≥ ε/2} :=
--            Measure.prod_swap ...
--          ```
--
--       4. **Union bound:**
--          P[|gap| ≥ ε] ≤ P[gap ≥ ε] + P[gap ≤ -ε]
--                        ≤ 2·GF·exp(...) + 2·GF·exp(...)
--                        = 4·GF(C,2m)·exp(-mε²/8)
--          ```
--          -- Uses: MeasureTheory.measure_union_le for the union of two events
--          -- CAST: 2 * X + 2 * X = 4 * X in ENNReal (need ENNReal.add_mul or similar)
--          ```
--
--       **References:** SSBD Theorem 6.7, Kakade-Tewari Lecture 19
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1320-L1414
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1320-L1414

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal

theorem symmetrization_uc_bound {X : Type u} [MeasurableSpace X] [Infinite X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : Measurable c)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε)
    (hm_large : 2 * Real.log 2 ≤ ↑m * ε ^ 2)
    (hE_nullmeas : MeasureTheory.NullMeasurableSet
      {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
        EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
      ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
       (MeasureTheory.Measure.pi (fun _ : Fin m => D)))) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
           (zeroOneLoss Bool)| ≥ ε}
    ≤ ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * m)) *
        Real.exp (-(↑m * ε ^ 2 / 8))) := by sorry
