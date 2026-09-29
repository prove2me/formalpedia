-- Prove2me | solution 1 for mme_more_asymmetry_cofinal_hash_extraction_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T11:53:18.756475+00:00
-- url     : https://prove2.me/submissions/bdd70a28-77b5-46f8-8d86-28dbd9ab9a1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3
import Theorems.Thm_mme_more_asymmetry_recursive_assembly_from_forward_fields
import Theorems.Thm_mme_recursive_yz_certificate_finite_assembly
open BigOperators MME MME.HashExtraction MME.RecursiveYZ.Certificate Filter
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
    ∃ (D : ℕ → Data) (V : ℝ) (error : ℕ → ℝ),
      (2401 : ℝ) < V ∧
      Tendsto (fun n ↦ (D n).power) atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ j, ((D n).hash j).Budget) ∧
        (D n).Realizes K ∧
        (V ^ (6 : ℕ)) ^ (D n).power * (1 - error n) ≤
          (D n).rate ((3952233 : ℝ) / 5000000)  := by
  obtain ⟨D,A,V,error,hV,hpow,herr,hevent⟩ :=
    mme_more_asymmetry_cofinal_forward_fields_stage_rate_certificate_v3 (K := K)
  refine ⟨D,V,error,hV,hpow,herr,?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨hraw,a,b,c,htemplate,ha,hb,hc,hcopy,hstage,hrate⟩ := hn
  have hassembly := mme_more_asymmetry_recursive_assembly_from_forward_fields
    (D n) (A n) hraw a b c htemplate ha hb hc hcopy
  obtain ⟨hbudget,hrealizes⟩ := mme_recursive_yz_certificate_finite_assembly
    (K := K) (D n) (A n) hstage
  exact ⟨hbudget,hrealizes hassembly,hrate⟩
