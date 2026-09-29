-- Prove2me | Theorems.Thm_mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3
-- name    : mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3
-- status  : Open
-- author  : @WillR
-- created : 2026-09-12T18:09:16.638623+00:00
-- url     : https://prove2.me/theorems/39c88d59-61fc-4961-9823-3324a6b297f6
-- title:
--   More Asymmetry cofinal stage/rate certificate with forward assembly fields (parenthesized)
-- statement:
--   Construct one cofinal More Asymmetry family whose eventual stage/rate certificate exposes, for the same D n and A n, raw-source compatibility, explicit local matrix dimensions, forward local-MM-to-template restrictions, their product equalities, and the target-to-local repaired-copy restriction. Budgets, diverging powers, vanishing error, strict V, and the fixed-tau rate bound hold for those same witnesses. This corrected child does not assert RecursiveAssembly.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Vassilevska Williams, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5.1 and 6.1--6.6. The forward fields follow the exact orientation needed by RecursiveAssembly.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_stage_certificate
import Mathlib.Topology.Instances.Real.Lemmas

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter

set_option autoImplicit false

universe u

theorem mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3 {K : Type u} [Field K] :
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
                        (D n).rate ((3952233 : ℝ) / 5000000) := by sorry
