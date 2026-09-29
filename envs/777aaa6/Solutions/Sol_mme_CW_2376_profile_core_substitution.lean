-- Prove2me | solution 1 for mme_CW_2376_profile_core_substitution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:10:32.372378+00:00
-- url     : https://prove2.me/submissions/9dc131a6-3573-4d09-976c-df6b8fb0e84b

import Mathlib.Tactic
import Theorems.Thm_mme_CW_2376_profile_weight_arithmetic
import Theorems.Thm_mme_kronPow_kronPow_isomorphic
import Theorems.Thm_mme_MM_bigAdd_kronPow_substitution

open MME BigOperators

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (Vc : ℝ) (hVc_nonneg : 0 ≤ Vc)
    (m s : ℕ)
    (delta : ℝ) (hdelta_pos : 0 < delta) (hdelta_lt : delta < 1)
    (kc : ℕ) (xc yc zc : Fin kc → ℕ)
    (hc_restrict :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (xc i) (yc i) (zc i)))
        ((cyclicSymmetrization (coupledObj K 6)).kronPow m))
    (hc_weight :
      Vc ^ m * (1 - delta) ≤
        ∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau)) :
    ∃ (k : ℕ) (x y z : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
        (TensorObj.bigAdd
          (fun _ : Fin s => cw2376ProfileCore K m)) ∧
      (s : ℝ) *
          (cw2376ProfileNumeratorBase tau Vc ^ (3000000 * m)) *
          (1 - delta) ^ (616627 : ℕ) ≤
        ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  let C : TensorObj K 3 := cyclicSymmetrization (coupledObj K 6)
  let W : ℝ :=
    ∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau)
  have htau_nonneg : 0 ≤ tau := by linarith
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpower :
      TensorObj.Isomorphic
        (((C.kronPow m).kronPow 616627))
        (C.kronPow (616627 * m)) :=
    mme_kronPow_kronPow_isomorphic C m 616627
  obtain ⟨k, x, y, z, hrestrict, hweight⟩ :=
    mme_MM_bigAdd_kronPow_substitution
      (K := K) tau htau_nonneg 616627 s
      (cw2376ProfileSide m) (cw2376ProfileSide m)
      (cw2376ProfileSide m) kc xc yc zc
      (C.kronPow m) (C.kronPow (616627 * m))
      (by simpa [C] using hc_restrict) hpower
  have harith := mme_CW_2376_profile_weight_arithmetic
    tau htau Vc hVc_nonneg m delta hdelta_pos hdelta_lt
    W hW_nonneg (by simpa [W] using hc_weight)
  refine ⟨k, x, y, z, ?_, ?_⟩
  · simpa [cw2376ProfileCore, C] using hrestrict
  · calc
      (s : ℝ) *
            (cw2376ProfileNumeratorBase tau Vc ^ (3000000 * m)) *
            (1 - delta) ^ (616627 : ℕ)
          ≤ (s : ℝ) *
              (((((cw2376ProfileSide m * cw2376ProfileSide m *
                  cw2376ProfileSide m : ℕ) : ℝ) ^ tau) *
                W ^ (616627 : ℕ))) := by
            simpa only [mul_assoc] using
              (mul_le_mul_of_nonneg_left harith (Nat.cast_nonneg s))
      _ ≤ ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
        simpa [W] using hweight
