-- Prove2me | solution 1 for mme_more_asymmetry_cofinal_explicit_child_witness_from_forward_certificate_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-23T19:02:19.230108+00:00
-- url     : https://prove2.me/submissions/30ee2f06-9d09-4beb-b07e-19b0a403ee64
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_explicit_child_witness
import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Mathlib.Topology.Instances.Real.Lemmas

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] (hforward :
    ∃ (D : ℕ → Data)
      (A : ∀ n j, Stage ((D n).hash j))
      (V : ℝ)
      (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
          ∃ localA localB localC : Fin (D n).factors → ℕ,
            ∃ hfactor_template :
              ∀ j, TensorObj.Restrict
                (MMObj K (localA j) (localB j) (localC j))
                ((A n j).template K),
              ∃ hprod_a : (∏ j, localA j) = (D n).a,
                ∃ hprod_b : (∏ j, localB j) = (D n).b,
                  ∃ hprod_c : (∏ j, localC j) = (D n).c,
                    ∃ hcopy :
                      (∀ counts : Fin (D n).factors → ℕ,
                        (∀ j, ((D n).hash j).lower ≤ (counts j : ℝ)) →
                        TensorObj.Restrict
                          (TensorObj.bigAdd
                            (fun _ : Fin ((∏ j, counts j) / (D n).repairCopies) ↦
                              MMObj K (D n).a (D n).b (D n).c))
                          (TensorObj.kronFin (D n).factors
                            (fun j ↦ TensorObj.bigAdd
                              (fun _ : Fin (counts j / 8 ^ ((A n) j).repairExponent) ↦
                                MMObj K (localA j) (localB j) (localC j))))),
                      (∀ j, (A n j).Budget) ∧
                      (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
                        (D n).rate ((3952233 : ℝ) / 5000000)) :
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
  exact mme_more_asymmetry_cofinal_explicit_child_witness
