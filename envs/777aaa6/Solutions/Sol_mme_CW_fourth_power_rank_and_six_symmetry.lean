-- Prove2me | solution 1 for mme_CW_fourth_power_rank_and_six_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T17:01:28.08694+00:00
-- url     : https://prove2.me/submissions/0bb899f9-2dd7-4a39-b685-863c7afd096f

import Theorems.Thm_mme_CW_fourth_asymptoticRank_le
import Theorems.Thm_mme_CW_fourth_six_symmetrization_iso
import Theorems.Thm_mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q N : ℕ) (hN : 0 < N) :
    tensorAsymptoticRank ((MME.StothersFourth.cwFourthObj K q).kronPow N) ≤
        (((q : ℝ) + 2) ^ (4 : ℕ)) ^ N ∧
      TensorObj.Isomorphic
        (sixSymmetrization ((MME.StothersFourth.cwFourthObj K q).kronPow N))
        (((MME.StothersFourth.cwFourthObj K q).kronPow N).kronPow 6) := by
  constructor
  · have hnonneg : 0 ≤ tensorAsymptoticRank (MME.StothersFourth.cwFourthObj K q) := by
      unfold tensorAsymptoticRank
      exact le_ciInf fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [mme_tensorAsymptoticRank_kronPow_eq_of_two_le_of_pos
      (by decide) _ N (Nat.succ_le_of_lt hN)]
    exact pow_le_pow_left₀ hnonneg (mme_CW_fourth_asymptoticRank_le q) N
  · apply ((mme_sixSymmetrization_kronPow_isomorphic
      (MME.StothersFourth.cwFourthObj K q) N).symm).trans
    apply TensorQ.toQ_eq_iff.mp
    simp only [TensorQ.toQ_kronPow]
    rw [TensorQ.toQ_eq_iff.mpr (mme_CW_fourth_six_symmetrization_iso q),
      TensorQ.toQ_kronPow, ← pow_mul, ← pow_mul, Nat.mul_comm]
