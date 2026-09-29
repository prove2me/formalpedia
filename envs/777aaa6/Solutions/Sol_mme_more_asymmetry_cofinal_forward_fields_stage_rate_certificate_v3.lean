-- Prove2me | solution 1 for mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T12:13:38.029547+00:00
-- url     : https://prove2.me/submissions/1d4ce5fc-f334-4424-9e68-a716dfc305cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_cellwise_child_matrix_certificate
import Theorems.Thm_mme_recursive_yz_intact_template_MM_of_child_extractions
import Theorems.Thm_mme_finite_repaired_MM_product_from_copy_budgets
open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
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
                        (D n).rate ((3952233 : ℝ) / 5000000)  := by
  obtain ⟨D,A,V,error,hV,hpow,herr,hevent⟩ :=
    mme_more_asymmetry_cofinal_cellwise_child_matrix_certificate (K := K)
  refine ⟨D,A,V,error,hV,hpow,herr,?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨hraw,M,ha,hb,hc,hlower,hrepair,hbudget,hrate⟩ := hn
  refine ⟨hraw,(fun j ↦ (M j).dimA),(fun j ↦ (M j).dimB),(fun j ↦ (M j).dimC),
    (fun j ↦ mme_recursive_yz_intact_template_MM_of_child_extractions (A n j) (M j)),
    ha,hb,hc,?_,hbudget,hrate⟩
  intro counts hcounts
  have henough (j : Fin (D n).factors) : 8 ^ (A n j).repairExponent ≤ counts j := by
    exact_mod_cast (hlower j).trans (hcounts j)
  have h := mme_finite_repaired_MM_product_from_copy_budgets
    (K := K) (fun j ↦ (M j).dimA) (fun j ↦ (M j).dimB) (fun j ↦ (M j).dimC)
    counts (fun j ↦ 8 ^ (A n j).repairExponent)
    (fun j ↦ pow_pos (by decide) _) henough hrepair
  simpa only [ha,hb,hc] using h
