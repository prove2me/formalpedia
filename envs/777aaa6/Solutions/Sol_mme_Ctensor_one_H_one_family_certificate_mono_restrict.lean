-- Prove2me | solution 1 for mme_Ctensor_one_H_one_family_certificate_mono_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:47:01.496426+00:00
-- url     : https://prove2.me/submissions/396096e5-7fb9-47a0-ad3b-90f843354ebf

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_tensor_quotient

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {S T : TensorObj K 3} {A H volume : ℕ}
    (stars : Nonempty (CTensorOneHOneFamilyCertificate T A H volume))
    (hTS : TensorObj.Restrict T S) :
    Nonempty (CTensorOneHOneFamilyCertificate S A H volume) := by
  rcases stars with ⟨stars⟩
  exact ⟨{
    star := stars.star
    restrict := TensorObj.Restrict.trans stars.restrict hTS
    certificate := stars.certificate
  }⟩
