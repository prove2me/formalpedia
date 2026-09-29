-- Prove2me | solution 1 for mme_CW_fourth_asymptoticRank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T15:57:58.701204+00:00
-- url     : https://prove2.me/submissions/f4185c6e-4057-4495-ae90-a104afcad435

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_CW_square_asymptoticRank_le
import Theorems.Thm_mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
import Theorems.Thm_mme_tensorAsymptoticRank_mono_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    tensorAsymptoticRank (MME.StothersFourth.cwFourthObj K q) ≤
      ((q : ℝ) + 2) ^ (4 : ℕ) := by
  let S : TensorObj K 3 := TensorObj.kron (CWObj K q) (CWObj K q)
  have hsource : TensorObj.Isomorphic
      (MME.StothersFourth.cwFourthObj K q) (S.kronPow 2) := by
    apply TensorQ.toQ_eq_iff.mp
    change TensorQ.toQ (TensorObj.kron S S) = TensorQ.toQ (S.kronPow 2)
    rw [TensorQ.toQ_kron, TensorQ.toQ_kronPow, pow_two]
  have hS : tensorAsymptoticRank S ≤ ((q : ℝ) + 2) ^ (2 : ℕ) :=
    mme_CW_square_asymptoticRank_le q
  have hnonneg : 0 ≤ tensorAsymptoticRank S := by
    unfold tensorAsymptoticRank
    exact le_ciInf fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    tensorAsymptoticRank (MME.StothersFourth.cwFourthObj K q) ≤
        tensorAsymptoticRank (S.kronPow 2) :=
      mme_tensorAsymptoticRank_mono_restrict hsource.1
    _ = tensorAsymptoticRank S ^ (2 : ℕ) :=
      mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos (by decide) S 2 (by decide)
    _ ≤ (((q : ℝ) + 2) ^ (2 : ℕ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hnonneg hS 2
    _ = ((q : ℝ) + 2) ^ (4 : ℕ) := by ring
