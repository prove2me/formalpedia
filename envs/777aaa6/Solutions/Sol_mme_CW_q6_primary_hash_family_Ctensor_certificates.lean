-- Prove2me | solution 1 for mme_CW_q6_primary_hash_family_Ctensor_certificates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:50:53.716063+00:00
-- url     : https://prove2.me/submissions/32b2a037-c74c-493f-af41-c563f0fcf054

import Theorems.Thm_mme_CW_coupled_three_grading_isomorphism_certificate
import Theorems.Thm_mme_coupled_four_block_induced_family_Ctensor_certificates_design

open MME

universe u

theorem solution
    {K : Type u} [Field K]
    (N L G A H : ℕ) (family : CWQ6PrimaryHashFamily N L G A H) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        ((coupledObj K 6).kronPow (2 * N))
        A H (6 ^ (4 * G + 2 * L))) := by
  obtain ⟨grading, hSupport, h000, h111, h012, h102⟩ :=
    mme_CW_coupled_three_grading_isomorphism_certificate (K := K) 6
  exact mme_coupled_four_block_induced_family_Ctensor_certificates_design
    6 N L G A H (coupledObj K 6) grading hSupport
      h000 h111 h012 h102 family
