-- Prove2me | solution 1 for mme_stothers_fourth_fixed_tau_value_23737
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:23:52.551828+00:00
-- url     : https://prove2.me/submissions/be36b95b-19ab-4f30-82c2-630b43d34d4d

import Theorems.Thm_mme_stothers_fixed_profile_numeric_surplus
import Theorems.Thm_mme_stothers_fixed_profile_fourth_value_below_globalRate
import Theorems.Thm_mme_HasTauValueAtLeast_kronPow_root
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_tensor_quotient

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.M5Numeric

/-- The definition-backed fixed profile is exactly the literal rational
vector used by the standalone numerical certificate. -/
theorem fixedProfileB_explicit :
    fixedProfileB =
      ![(98 : ℝ) / 97942072,
        (1862 : ℝ) / 97942072,
        (73075 : ℝ) / 97942072,
        (1023050 : ℝ) / 97942072,
        (3626000 : ℝ) / 97942072,
        (98000 : ℝ) / 97942072,
        (2156000 : ℝ) / 97942072,
        (13720000 : ℝ) / 97942072,
        (21560000 : ℝ) / 97942072,
        (38710000 : ℝ) / 97942072] := by
  funext i
  fin_cases i <;>
    norm_num [fixedProfileB, fixedProfileBaseCount, fixedProfileScale]

/-- The literal fourth CW power is isomorphic to the recursively represented
second power of the literal CW square. -/
theorem cwFourthObj_isomorphic_square_kronPow_two
    {K : Type u} [Field K] :
    TensorObj.Isomorphic
      (cwFourthObj K 6)
      ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow 2) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [cwFourthObj, TensorObj.kronPow]
  let S : TensorObj K 3 := TensorObj.kron (CWObj K 6) (CWObj K 6)
  change TensorQ.toQ (TensorObj.kron S S) =
    TensorQ.toQ (TensorObj.kron S (TensorObj.kron S TensorObj.oneObj))
  calc
    TensorQ.toQ (TensorObj.kron S S) =
        TensorQ.toQ S * TensorQ.toQ S := (TensorQ.toQ_mul S S).symm
    _ = TensorQ.toQ S * (TensorQ.toQ S * (1 : TensorQ K 3)) := by
      exact congrArg (fun z ↦ TensorQ.toQ S * z)
        (@mul_one (TensorQ K 3)
          TensorQ.instCommSemiring.toMulOneClass (TensorQ.toQ S)).symm
    _ = TensorQ.toQ
        (TensorObj.kron S (TensorObj.kron S TensorObj.oneObj)) := by
      rw [TensorQ.toQ_one, TensorQ.toQ_mul, TensorQ.toQ_mul]

/-- A fourth-power value at a squared scalar descends to the literal square. -/
theorem square_value_of_fourth_value
    {K : Type u} [Field K] (tau V : ℝ) (hV : 0 ≤ V)
    (hfourth :
      HasTauValueAtLeast (cwFourthObj K 6) tau (V ^ (2 : ℕ))) :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6)) tau V := by
  let S : TensorObj K 3 := TensorObj.kron (CWObj K 6) (CWObj K 6)
  have hpower : HasTauValueAtLeast (S.kronPow 2) tau (V ^ (2 : ℕ)) :=
    mme_HasTauValueAtLeast_mono_restrict
      cwFourthObj_isomorphic_square_kronPow_two.1 hfourth
  exact mme_HasTauValueAtLeast_kronPow_root S tau V 2
    (by norm_num) hV hpower

end MME.StothersFourth.M5Numeric

/-- Verifier-ready reduction of Milestone 5 to the exact numerical surplus,
the fixed-profile fourth-power extraction, and the proved generic
fourth-to-square value bridges. -/
theorem solution
    {K : Type u} [Field K] :
    HasTauValueAtLeast
      (TensorObj.kron (CWObj K 6) (CWObj K 6))
      (23737 / 30000) (640000001 / 10000000) := by
  have hscalar :
      (640000001 / 10000000 : ℝ) ^ (2 : ℕ) <
        MME.StothersFourth.globalRate
          6 (23737 / 30000)
          MME.StothersFourth.fixedProfileB
          MME.StothersFourth.fixedProfileB := by
    rw [MME.StothersFourth.M5Numeric.fixedProfileB_explicit]
    simpa only using
      mme_stothers_fixed_profile_numeric_surplus
  have hfourth :
      HasTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 6)
        (23737 / 30000)
        ((640000001 / 10000000 : ℝ) ^ (2 : ℕ)) :=
    mme_stothers_fixed_profile_fourth_value_below_globalRate
      (K := K) _ (by positivity) hscalar
  exact MME.StothersFourth.M5Numeric.square_value_of_fourth_value
    (K := K) (23737 / 30000) (640000001 / 10000000)
    (by norm_num) hfourth
