-- Prove2me | solution 2 for mme_more_asymmetry_cofinal_cellwise_child_matrix_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T23:12:34.190982+00:00
-- url     : https://prove2.me/submissions/362cce7d-793c-4790-ac33-4fe1cd9c6d22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_child_matrix_data
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_mme_more_asymmetry_cellwise_cofinal_from_finite_seed
import Theorems.Thm_mme_more_asymmetry_cellwise_finite_seed_exists

open BigOperators MME MME.TensorObj MME.HashExtraction
  MME.RecursiveYZ.Certificate Filter

set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j))
      (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
          ∃ M : ∀ j, (A n j).ChildMM K,
            (∏ j, (M j).dimA) = (D n).a ∧
            (∏ j, (M j).dimB) = (D n).b ∧
            (∏ j, (M j).dimC) = (D n).c ∧
            (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤
              ((D n).hash j).lower) ∧
            (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
            (∀ j, (A n j).Budget) ∧
            (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
              (D n).rate ((3952233 : ℝ) / 5000000) := by
  exact mme_more_asymmetry_cellwise_cofinal_from_finite_seed
    (K := K)
    (mme_more_asymmetry_cellwise_finite_seed_exists (K := K))
