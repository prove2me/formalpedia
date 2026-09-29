-- Prove2me | solution 1 for mme_CW_fourth_six_symmetrization_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T15:57:58.698816+00:00
-- url     : https://prove2.me/submissions/2adf6518-b5c0-409e-b6df-06a59eaf05b9

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_CW_square_six_symmetrization_iso
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization (MME.StothersFourth.cwFourthObj K q))
      ((MME.StothersFourth.cwFourthObj K q).kronPow 6) := by
  let S : TensorObj K 3 := TensorObj.kron (CWObj K q) (CWObj K q)
  have hsource : TensorObj.Isomorphic
      (MME.StothersFourth.cwFourthObj K q) (S.kronPow 2) := by
    apply TensorQ.toQ_eq_iff.mp
    change TensorQ.toQ (TensorObj.kron S S) = TensorQ.toQ (S.kronPow 2)
    rw [TensorQ.toQ_kron, TensorQ.toQ_kronPow, pow_two]
  have hsymSource : TensorObj.Isomorphic
      (sixSymmetrization (MME.StothersFourth.cwFourthObj K q))
      (sixSymmetrization (S.kronPow 2)) :=
    ⟨mme_sixSymmetrization_restrict hsource.1,
      mme_sixSymmetrization_restrict hsource.2⟩
  have hbase : TensorObj.Isomorphic (sixSymmetrization S) (S.kronPow 6) :=
    mme_CW_square_six_symmetrization_iso q
  apply hsymSource.trans
    ((mme_sixSymmetrization_kronPow_isomorphic S 2).symm.trans ?_)
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_kronPow, TensorQ.toQ_kronPow,
    TensorQ.toQ_eq_iff.mpr hbase, TensorQ.toQ_kronPow]
  change ((TensorQ.toQ S) ^ (6 : ℕ)) ^ (2 : ℕ) =
    (TensorQ.toQ (TensorObj.kron S S)) ^ (6 : ℕ)
  rw [TensorQ.toQ_kron S S]
  ring
