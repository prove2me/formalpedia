-- Prove2me | solution 2 for mme_more_asymmetry_cofinal_repaired_template_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T11:43:06.903201+00:00
-- url     : https://prove2.me/submissions/79351442-6a5f-457d-b9ad-7a9d6a3e13f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3
import Theorems.Thm_mme_more_asymmetry_recursive_assembly_from_forward_fields

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
    ∃ (D : ℕ → Data) (A : ∀ n j, Stage ((D n).hash j)) (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ j, (A n j).Budget) ∧
        RecursiveAssembly (D n) (A n) K ∧
        (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
          (D n).rate ((3952233 : ℝ) / 5000000)  := by
  obtain ⟨D, A, V, error, hV, hpower, herror, hevent⟩ :=
    mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3 (K := K)
  refine ⟨D, A, V, error, hV, hpower, herror, ?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨hraw, a, b, c, htemplate, ha, hb, hc, hcopy, hbudget, hrate⟩ := hn
  exact ⟨hbudget,
    mme_more_asymmetry_recursive_assembly_from_forward_fields
      (D n) (A n) hraw a b c htemplate ha hb hc hcopy, hrate⟩
