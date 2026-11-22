-- Prove2me | Theorems.Thm_nfl_counting_core
-- name    : nfl_counting_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:33:42.775747+00:00
-- url     : https://prove2.me/theorems/a09e6085-be0f-43b7-acfa-bbcbf398140a
-- title:
--   nfl counting core: nfl counting core
-- statement:
--   NFL counting core: for a shattered set T with |T| > 2m, there exists a labeling
--       f₀ : ↥T → Bool and its shattering witness c₀ ∈ C such that the number of
--       samples xs : Fin m → ↥T where the learner achieves low error (≤ |T|/4) is
--       at most half the total number of samples.
--       Proof: double-counting + pigeonhole using per_sample_labeling_bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1236-L1343
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Generalization/Core.lean#L1236-L1343

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

theorem nfl_counting_core {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) {m : ℕ} (h2m : 2 * m < T.card)
    (L : BatchLearner X Bool) :
    ∃ (f₀ : ↥T → Bool),
      ∃ (c₀ : Concept X Bool), c₀ ∈ C ∧ (∀ t : ↥T, c₀ (↑t) = f₀ t) ∧
        2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
          (Finset.univ.filter fun t : ↥T =>
            c₀ ((↑t : X)) ≠
              L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
          ≤ T.card).card
        ≤ Fintype.card (Fin m → ↥T) := by sorry
