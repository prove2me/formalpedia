-- Prove2me | solution 1 for mme_CW_six_symmetrized_power_four_mul_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:20:45.190827+00:00
-- url     : https://prove2.me/submissions/4b96f2c9-571d-421c-a1a4-6ca5331c79f0

import Theorems.Thm_mme_CW_six_fourth_power_isomorphic
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict

open MME
universe u
set_option autoImplicit false

/-- Symmetrizing a power with four times as many elementary CW factors
gives exactly twenty-four times as many factors. -/
theorem solution
    {K : Type u} [Field K] (q N : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization ((CWObj K q).kronPow (4 * N)))
      ((CWObj K q).kronPow (24 * N)) := by
  have hfourth : TensorObj.Isomorphic
      ((StothersFourth.cwFourthObj K q).kronPow N)
      ((CWObj K q).kronPow (4 * N)) := by
    apply TensorQ.toQ_eq_iff.1
    have hf : TensorQ.toQ (StothersFourth.cwFourthObj K q) =
        TensorQ.toQ (CWObj K q) ^ 4 := by
      simp only [StothersFourth.cwFourthObj, TensorQ.toQ_kron]
      ring
    rw [TensorQ.toQ_kronPow, TensorQ.toQ_kronPow, hf, pow_mul]
  have hs : TensorObj.Isomorphic
      (sixSymmetrization ((CWObj K q).kronPow (4 * N)))
      (sixSymmetrization ((StothersFourth.cwFourthObj K q).kronPow N)) :=
    ⟨mme_sixSymmetrization_restrict hfourth.2,
      mme_sixSymmetrization_restrict hfourth.1⟩
  exact hs.trans
    ((mme_sixSymmetrization_kronPow_isomorphic
      (StothersFourth.cwFourthObj K q) N).symm.trans
      (mme_CW_six_fourth_power_isomorphic q N))


#print axioms solution
