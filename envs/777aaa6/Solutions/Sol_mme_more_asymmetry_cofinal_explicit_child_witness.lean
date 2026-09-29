-- Prove2me | solution 1 for mme_more_asymmetry_cofinal_explicit_child_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-22T21:21:24.683177+00:00
-- url     : https://prove2.me/submissions/2cb7dbcc-a108-4c1a-a4d3-6d04a883aee8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3
import Theorems.Thm_mme_more_asymmetry_cofinal_explicit_child_witness_from_forward_certificate_v3

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter
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
          ∃ (a b c : ∀ j, Fin (A n j).childCells → ℕ),
            (∏ j, ∏ k, a j k) = (D n).a ∧
            (∏ j, ∏ k, b j k) = (D n).b ∧
            (∏ j, ∏ k, c j k) = (D n).c ∧
            (∀ j k,
              (A n j).BoundaryChild k (a j k) (b j k) (c j k) ∨
              ((∀ i, 0 < (((A n j).childCell k).2.val i).val) ∧
                TensorObj.Restrict
                  (MMObj K (a j k) (b j k) (c j k))
                  ((A n j).childTensor K k))) ∧
            (∀ j, ((8 ^ (A n j).repairExponent : ℕ) : ℝ) ≤ ((D n).hash j).lower) ∧
            (∏ j, 2 * 8 ^ (A n j).repairExponent) ≤ (D n).repairCopies ∧
            (∀ j, (A n j).Budget) ∧
            (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
              (D n).rate ((3952233 : ℝ) / 5000000) := by
  apply mme_more_asymmetry_cofinal_explicit_child_witness_from_forward_certificate_v3
  exact mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3 (K := K)
