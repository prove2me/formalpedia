-- Prove2me | solution 1 for mme_paired_Ctensor_certificate_to_six_symmetric_tau_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:40:21.379212+00:00
-- url     : https://prove2.me/submissions/b74e2485-4868-49d1-ab78-94b3c8ea3c89

import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_cyclic_value_below
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate
      (TensorObj.kron T (TensorObj.permObj swapFirstTwoPerm T))
      A H volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
      (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (sixSymmetrization T) tau V := by
  have hpaired :=
    mme_Ctensor_one_H_one_outer_family_cyclic_value_below
      stars tau htau V hV hVlt
  exact mme_HasTauValueAtLeast_mono_restrict
    (mme_sixSymmetrization_isomorphic_cyclic_paired_swap T).2 hpaired
