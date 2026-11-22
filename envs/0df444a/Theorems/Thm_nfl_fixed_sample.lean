-- Prove2me | Theorems.Thm_nfl_fixed_sample
-- name    : nfl_fixed_sample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:40:18.43181+00:00
-- url     : https://prove2.me/theorems/a6f4d675-088c-4939-8575-f5fcaa1b2692
-- title:
--   nfl fixed sample: nfl fixed sample
-- statement:
--   NFL for fixed sample size (Shalev-Shwartz & Ben-David Theorem 5.1):
--       For any fixed sample size m, there exists a distribution such that
--       any learner using m samples fails on SOME concept in Set.univ.
--
--       The distribution is bundled with its probability-measure proof, avoiding
--       a weak implication-shaped existence statement.
--
--       Proof route:
--       1. Let T ⊂ X with |T| = 2m (exists since 2m ≤ |X|)
--       2. D = uniform over T: D = (1 / 2m) · Σ_{x ∈ T} δ_x
--       3. For any learner L, average over random labelings c : T → Bool:
--          E_c[TrueError(L(S), c, D)] ≥ 1 / 4 (the unseen points are random)
--       4. By Markov: ∃ c with TrueError > 1 / 8 with positive probability
--
--       KU₂₁: Constructing uniform measure on T requires Fintype instance
--       or manual construction via Finset.sum of Dirac measures.
--       UK₁₀: The averaging-over-labelings step is where the counting argument
--       lives — this is combinatorial, not measure-theoretic.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L386-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Theorem/PAC.lean#L386-L403

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Compression
public import Definitions.Def_LeanPool_FormalLearningTheory_Bridge
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Measurability
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GeneralizationResults
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_PAC
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem nfl_fixed_sample (X : Type u) [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X]
    (hX : 2 ≤ Fintype.card X) (m : ℕ) (hm : 2 * m ≤ Fintype.card X)
    (L : BatchLearner X Bool) :
    ∃ (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ∧
      ∃ (c : X → Bool),
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              > ENNReal.ofReal (1 / 8) }
          > 0 := by sorry
