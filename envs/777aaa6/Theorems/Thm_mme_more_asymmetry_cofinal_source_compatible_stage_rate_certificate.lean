-- Prove2me | Theorems.Thm_mme_more_asymmetry_cofinal_source_compatible_stage_rate_certificate
-- name    : mme_more_asymmetry_cofinal_source_compatible_stage_rate_certificate
-- status  : Open
-- author  : @WillR
-- created : 2026-09-12T17:36:57.143437+00:00
-- url     : https://prove2.me/theorems/4ff60052-7bed-48e1-8f01-b21302beea45
-- title:
--   More Asymmetry cofinal stage/rate certificate with shared assembly data
-- statement:
--   Construct one cofinal More Asymmetry family whose data/rate certificate exposes, for the same D n and A n, raw-source compatibility and intact-template/MM compatibility together with the finite repaired-copy restriction. The stage budgets, diverging source powers, vanishing error, strict V bound, and fixed-tau rate inequality hold eventually for those same witnesses. This is the corrected data child: it does not assert RecursiveAssembly; the separate assembly theorem composes its explicitly exposed hypotheses.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 5.1 and 6.1--6.6. The cofinal construction exposes the finite source-compatible data required by the separate raw/template assembly composition.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_more_asymmetry_template_mm_compatibility
import Definitions.Def_mme_recursive_yz_stage_certificate
import Mathlib.Topology.Instances.Real.Lemmas

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter

set_option autoImplicit false

universe u

theorem mme_more_asymmetry_cofinal_source_compatible_stage_rate_certificate {K : Type u} [Field K] :
    ∃ (D : ℕ → Data)
      (A : ∀ n j, Stage ((D n).hash j))
      (V : ℝ)
      (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ hraw : MoreAsymmetryRawSourceCompatibility (D n) (A n) K,
          ∃ htemplate : MoreAsymmetryTemplateMMCompatibility (D n) (A n) K,
            (∀ j, (A n j).Budget) ∧
            (∀ counts : Fin (D n).factors → ℕ,
              (∀ j, ((D n).hash j).lower ≤ (counts j : ℝ)) →
              TensorObj.Restrict
                (TensorObj.bigAdd
                  (fun _ : Fin ((∏ j, counts j) / (D n).repairCopies) ↦
                    MMObj K (D n).a (D n).b (D n).c))
                (TensorObj.kronFin (D n).factors
                  (fun j ↦ TensorObj.bigAdd
                    (fun _ : Fin (counts j / 8 ^ ((A n) j).repairExponent) ↦
                      MMObj K (htemplate.localA j) (htemplate.localB j)
                        (htemplate.localC j))))) ∧
            (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
              (D n).rate ((3952233 : ℝ) / 5000000) := by sorry
