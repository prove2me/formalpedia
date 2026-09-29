-- Prove2me | solution 1 for mme_matrix_extraction_six_volume_weight
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:21:15.167204+00:00
-- url     : https://prove2.me/submissions/ea0fd4bf-8ab6-43d3-98a2-b431dab9963f

import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_sixSymmetrization_restrict

open MME
set_option autoImplicit false
universe u

/-- Full symmetrization turns a matrix tensor of volume V into a square
matrix tensor with each dimension V squared. -/
private theorem mme_MMObj_sixSymmetrization_iso {K : Type u} [Field K] (a b c : ℕ) :
    TensorObj.Isomorphic (sixSymmetrization (MMObj K a b c))
      (MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2) ((a * b * c) ^ 2)) := by
  let V := a * b * c
  have hcyc := TensorQ.toQ_eq_iff.mpr
    (mme_MMObj_cyclicSymmetrization_iso (K := K) a b c)
  have hswap := TensorQ.toQ_eq_iff.mpr
    (mme_MMObj_permObj_swapFirstTwo (K := K) V V V)
  apply TensorQ.toQ_eq_iff.mp
  rw [sixSymmetrization, TensorQ.toQ_kron, ← TensorQ.permAut_toQ,
    hcyc, TensorQ.permAut_toQ, hswap]
  have hmul := TensorQ.toQ_eq_iff.mpr (MMObj_kron_iso (K := K) V V V V V V)
  simpa only [TensorQ.toQ_kron, pow_two] using hmul

/-- A positive matrix extraction yields a six-symmetric extraction whose tau
weight retains six times its log-volume bound, for nonnegative tau. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} (a b c : ℕ)
    (hrestrict : TensorObj.Restrict (MMObj K a b c) T)
    (hpos : 0 < a * b * c) (rate tau : ℝ) (htau : 0 ≤ tau)
    (hrate : rate ≤ Real.log (a * b * c : ℕ)) :
    TensorObj.Restrict
      (MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2) ((a * b * c) ^ 2))
      (sixSymmetrization T) ∧
    Real.exp (6 * tau * rate) ≤
      ((((a * b * c) ^ 2 * (a * b * c) ^ 2 * (a * b * c) ^ 2 : ℕ) : ℝ) ^ tau) := by
  constructor
  · exact (mme_MMObj_sixSymmetrization_iso (K := K) a b c).2.trans
      (mme_sixSymmetrization_restrict hrestrict)
  · have hv : (0 : ℝ) < (a * b * c : ℕ) := by exact_mod_cast hpos
    have hpow : (a * b * c) ^ 2 * (a * b * c) ^ 2 * (a * b * c) ^ 2 =
        (a * b * c) ^ 6 := by ring
    rw [hpow, Nat.cast_pow, Real.rpow_def_of_pos (pow_pos hv _), Real.log_pow]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hrate (show 0 ≤ 6 * tau by positivity)]


#print axioms solution
