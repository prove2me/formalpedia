-- Prove2me | Theorems.Thm_growth_exp_le_delta
-- name    : growth_exp_le_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:40.491426+00:00
-- url     : https://prove2.me/theorems/5496afe7-2a0b-41cb-952f-81b09ec7de8e
-- title:
--   growth exp le delta: growth exp le delta
-- statement:
--   The growth exp le delta construction uses the growth exp le delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1556-L1702
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L1556-L1702

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

theorem growth_exp_le_delta {X : Type u}
    (C : ConceptClass X Bool)
    (v : ℕ) (hv : 0 < v) (m : ℕ) (hm : 0 < m) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hv_bound : ∀ (n : ℕ), v ≤ n →
      GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i)
    (hm_bound : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ ↑m) :
    4 * ↑(GrowthFunction X C (2 * m)) * Real.exp (-(↑m * ε ^ 2 / 8)) ≤ δ ∧
    2 * Real.log 2 ≤ ↑m * ε ^ 2 := by sorry
