-- Prove2me | solution 1 for mme_more_asymmetry_six_symmetric_tau_value_surplus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T09:03:20.203773+00:00
-- url     : https://prove2.me/submissions/27883d8c-3a52-4117-ba86-fb9964926264
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_more_asymmetry_cofinal_hash_extraction_certificate
import Theorems.Thm_mme_hash_extraction_finite_assembly
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME
universe u
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5)
        ((3952233 : ℝ) / 5000000) V := by
  obtain ⟨D,V,error,hV,hpower,herror,hcertificate⟩ :=
    mme_more_asymmetry_cofinal_hash_extraction_certificate (K := K)
  refine ⟨V,hV,?_⟩
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (sixSymmetrization (MME.StothersFourth.cwFourthObj K 5))
    ((3952233 : ℝ) / 5000000) (V ^ (6 : ℕ)) (by positivity)
    (fun n ↦ (D n).power) hpower error herror
  filter_upwards [hcertificate] with n hn
  obtain ⟨k,a,b,c,hrestrict,hvolume⟩ :=
    mme_hash_extraction_finite_assembly (K := K) (D n)
      ((3952233 : ℝ) / 5000000) hn.1 hn.2.1
  exact ⟨k,a,b,c,hrestrict,hn.2.2.trans hvolume⟩
