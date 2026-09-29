-- Prove2me | solution 1 for mme_CW_2376_grouped_square_blocks_dominate_profile_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T18:07:59.538715+00:00
-- url     : https://prove2.me/submissions/fbdc9fad-985f-40bb-a8e5-1f34256e248b

import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_CW_2376_address_block
import Theorems.Thm_mme_CW_2376_profile_product_split_univ

open MME BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

private theorem tq_mul_mono
    {K : Type u} [Field K]
    {a b c d : TensorQ K 3}
    (hab : TensorQ.le a b) (hcd : TensorQ.le c d) :
    TensorQ.le (a * c) (b * d) := by
  apply TensorQ.le_trans (a * c) (b * c) (b * d)
  · exact (tensorPreorder K).mul_right a b hab c
  · simpa [mul_comm] using
      ((tensorPreorder K).mul_right c d hcd b)

private theorem tq_pow_mono
    {K : Type u} [Field K]
    {a b : TensorQ K 3} (h : TensorQ.le a b) :
    ∀ n : ℕ, TensorQ.le (a ^ n) (b ^ n)
  | 0 => TensorQ.le_refl 1
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact tq_mul_mono (tq_pow_mono h n) h

private theorem MMq_pow
    {K : Type u} [Field K] (n p q r : ℕ) :
    (MMq K n p q) ^ r = MMq K (n ^ r) (p ^ r) (q ^ r) := by
  induction r with
  | zero => simp [MMq_one]
  | succ r ih => simp [pow_succ, ih, MMq_mul]

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6) (m : ℕ) :
    TensorQ.le
      (TensorQ.toQ (cw2376ProfileCore K m))
      (∏ σ : Fin 3 → Fin 5,
        (TensorQ.toQ (cert.grading.blockSubtensor σ)) ^
          cw2376ProfileMultiplicity m σ) := by
  classical
  let Q : (Fin 3 → Fin 5) → TensorQ K 3 :=
    fun σ => TensorQ.toQ (cert.grading.blockSubtensor σ)

  have h004 : TensorQ.le 1 (Q (cwSquareBlockType 0 0 4)) := by
    have h := (TensorQ.le_toQ
      (MMObj K 1 1 1)
      (cert.grading.blockSubtensor (cwSquareBlockType 0 0 4))).2
      cert.scalar004
    change TensorQ.le (MMq K 1 1 1)
      (Q (cwSquareBlockType 0 0 4)) at h
    simpa only [MMq_one] using h
  have h040 : TensorQ.le 1 (Q (cwSquareBlockType 0 4 0)) := by
    have h := (TensorQ.le_toQ
      (MMObj K 1 1 1)
      (cert.grading.blockSubtensor (cwSquareBlockType 0 4 0))).2
      cert.scalar040
    change TensorQ.le (MMq K 1 1 1)
      (Q (cwSquareBlockType 0 4 0)) at h
    simpa only [MMq_one] using h
  have h400 : TensorQ.le 1 (Q (cwSquareBlockType 4 0 0)) := by
    have h := (TensorQ.le_toQ
      (MMObj K 1 1 1)
      (cert.grading.blockSubtensor (cwSquareBlockType 4 0 0))).2
      cert.scalar400
    change TensorQ.le (MMq K 1 1 1)
      (Q (cwSquareBlockType 4 0 0)) at h
    simpa only [MMq_one] using h

  have h013 : TensorQ.le (MMq K 1 1 12)
      (Q (cwSquareBlockType 0 1 3)) := by
    simpa only [Q, show 2 * 6 = 12 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.rect013
  have h031 : TensorQ.le (MMq K 1 1 12)
      (Q (cwSquareBlockType 0 3 1)) := by
    simpa only [Q, show 2 * 6 = 12 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.rect031
  have h103 : TensorQ.le (MMq K 12 1 1)
      (Q (cwSquareBlockType 1 0 3)) := by
    simpa only [Q, show 2 * 6 = 12 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.rect103
  have h301 : TensorQ.le (MMq K 12 1 1)
      (Q (cwSquareBlockType 3 0 1)) := by
    simpa only [Q, show 2 * 6 = 12 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.rect301
  have h130 : TensorQ.le (MMq K 1 12 1)
      (Q (cwSquareBlockType 1 3 0)) := by
    simpa only [Q, show 2 * 6 = 12 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.rect130
  have h310 : TensorQ.le (MMq K 1 12 1)
      (Q (cwSquareBlockType 3 1 0)) := by
    simpa only [Q, show 2 * 6 = 12 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.rect310

  have h022 : TensorQ.le (MMq K 1 1 38)
      (Q (cwSquareBlockType 0 2 2)) := by
    simpa only [Q, show 6 ^ 2 + 2 = 38 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.central022
  have h202 : TensorQ.le (MMq K 38 1 1)
      (Q (cwSquareBlockType 2 0 2)) := by
    simpa only [Q, show 6 ^ 2 + 2 = 38 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.central202
  have h220 : TensorQ.le (MMq K 1 38 1)
      (Q (cwSquareBlockType 2 2 0)) := by
    simpa only [Q, show 6 ^ 2 + 2 = 38 by norm_num] using
      (TensorQ.le_toQ _ _).2 cert.central220

  have hcoupled :
      TensorQ.le (TensorQ.toQ (cyclicSymmetrization (coupledObj K 6)))
        (Q (cwSquareBlockType 1 1 2) *
          (Q (cwSquareBlockType 2 1 1) *
            Q (cwSquareBlockType 1 2 1))) := by
    have h := (TensorQ.le_toQ _ _).2 cert.coupledCyclic
    simpa only [Q, TensorQ.toQ_kron] using h

  have hscalar : TensorQ.le 1
      (∏ σ ∈ cw2376ScalarTypes, Q σ) := by
    rw [cw2376ScalarTypes]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    simp only [Finset.prod_singleton]
    simpa only [one_mul] using
      tq_mul_mono h004 (tq_mul_mono h040 h400)

  have hrect : TensorQ.le (MMq K 144 144 144)
      (∏ σ ∈ cw2376RectTypes, Q σ) := by
    rw [cw2376RectTypes]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    simp only [Finset.prod_singleton]
    have h := tq_mul_mono h013
      (tq_mul_mono h031
        (tq_mul_mono h103
          (tq_mul_mono h301 (tq_mul_mono h130 h310))))
    simpa only [MMq_mul, Nat.one_mul, Nat.mul_one] using h

  have hcentral : TensorQ.le (MMq K 38 38 38)
      (∏ σ ∈ cw2376CentralTypes, Q σ) := by
    rw [cw2376CentralTypes]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    simp only [Finset.prod_singleton]
    have h := tq_mul_mono h022 (tq_mul_mono h202 h220)
    simpa only [MMq_mul, Nat.one_mul, Nat.mul_one] using h

  have h12pow :
      144 ^ (37518 * m) = 12 ^ (75036 * m) := by
    rw [show 144 = 12 ^ 2 by norm_num, ← pow_mul]
    congr 1
    omega

  have hscalarPow : TensorQ.le 1
      ((∏ σ ∈ cw2376ScalarTypes, Q σ) ^ (699 * m)) := by
    simpa only [one_pow] using tq_pow_mono hscalar (699 * m)

  have hrectPow :
      TensorQ.le
        (MMq K (12 ^ (75036 * m)) (12 ^ (75036 * m))
          (12 ^ (75036 * m)))
        ((∏ σ ∈ cw2376RectTypes, Q σ) ^ (37518 * m)) := by
    have h := tq_pow_mono hrect (37518 * m)
    rw [MMq_pow] at h
    simpa only [h12pow] using h

  have hcentralPow :
      TensorQ.le
        (MMq K (38 ^ (307638 * m)) (38 ^ (307638 * m))
          (38 ^ (307638 * m)))
        ((∏ σ ∈ cw2376CentralTypes, Q σ) ^ (307638 * m)) := by
    have h := tq_pow_mono hcentral (307638 * m)
    rw [MMq_pow] at h
    exact h

  have hmatrix :
      TensorQ.le
        (MMq K (cw2376ProfileSide m) (cw2376ProfileSide m)
          (cw2376ProfileSide m))
        (((∏ σ ∈ cw2376RectTypes, Q σ) ^ (37518 * m)) *
          ((∏ σ ∈ cw2376CentralTypes, Q σ) ^ (307638 * m))) := by
    have h := tq_mul_mono hrectPow hcentralPow
    simpa only [MMq_mul, cw2376ProfileSide] using h

  have hcoupledPow :
      TensorQ.le
        ((TensorQ.toQ (cyclicSymmetrization (coupledObj K 6))) ^
          (616627 * m))
        ((Q (cwSquareBlockType 1 1 2) *
          (Q (cwSquareBlockType 2 1 1) *
            Q (cwSquareBlockType 1 2 1))) ^ (616627 * m)) :=
    tq_pow_mono hcoupled (616627 * m)

  have hcoupledProduct :
      (∏ σ ∈ cw2376CoupledTypes, Q σ) =
        Q (cwSquareBlockType 1 1 2) *
          (Q (cwSquareBlockType 2 1 1) *
            Q (cwSquareBlockType 1 2 1)) := by
    rw [cw2376CoupledTypes]
    rw [Finset.prod_insert (by decide)]
    rw [Finset.prod_insert (by decide)]
    simp only [Finset.prod_singleton]

  have hfinal := tq_mul_mono hscalarPow
    (tq_mul_mono hmatrix hcoupledPow)
  rw [cw2376ProfileCore, TensorQ.toQ_kron,
    TensorQ.toQ_kronPow]
  change TensorQ.le
    (MMq K (cw2376ProfileSide m) (cw2376ProfileSide m)
      (cw2376ProfileSide m) *
        TensorQ.toQ (cyclicSymmetrization (coupledObj K 6)) ^
          (616627 * m))
    (∏ σ, Q σ ^ cw2376ProfileMultiplicity m σ)
  rw [mme_CW_2376_profile_product_split_univ Q m]
  rw [hcoupledProduct]
  simpa only [one_mul, mul_assoc] using hfinal
