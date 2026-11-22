-- Prove2me | Theorems.Thm_nfl_per_sample_shattered
-- name    : nfl_per_sample_shattered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:38:22.771861+00:00
-- url     : https://prove2.me/theorems/deebde19-bdd4-433d-a55f-26759240632f
-- title:
--   nfl per sample shattered: nfl per sample shattered
-- statement:
--   NFL per-sample lemma for shattered sets: for ANY fixed sample xs and
--       ANY hypothesis h, there exists c ∈ C agreeing with h on sample points
--       but with high error (> 1 / 4) on the shattered set T.
--       Uses the counting argument on unseen points via disagreement_sum_eq.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L139-L188
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Tail.lean#L139-L188

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_VCDimension
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Tail
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem nfl_per_sample_shattered {X : Type u} {C : ConceptClass X Bool}
    {T : Finset X} (hT : Shatters X C T) {m : ℕ} (hTcard : 2 * m < T.card)
    (xs : Fin m → X) (h : X → Bool) :
    ∃ c ∈ C, (∀ i : Fin m, xs i ∈ T → c (xs i) = h (xs i)) ∧
      T.card < 4 * (T.filter fun x => c x ≠ h x).card := by sorry
