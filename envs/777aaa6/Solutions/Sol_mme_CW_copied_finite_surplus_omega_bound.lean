-- Prove2me | solution 1 for mme_CW_copied_finite_surplus_omega_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:01:57.744981+00:00
-- url     : https://prove2.me/submissions/1ca61d76-4267-4e66-aa94-0b52c96bbb9e

import Theorems.Thm_mme_CW_border_rank_le
import Theorems.Thm_mme_borderRank_kronPow_le
import Theorems.Thm_mme_degenerates_asymptoticRank_le
import Theorems.Thm_mme_tensorAsymptoticRank_mono_restrict
import Theorems.Thm_mme_asymptotic_sum_inequality
import Theorems.Thm_mme_omega_eq_strassen

open MME MME.TensorObj BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

private theorem repeated_rank_bound {K : Type u} [Field K]
    (T : TensorObj K 3) (r b : ℕ) (hT : tensorAsymptoticRank T ≤ b) :
    tensorAsymptoticRank (bigAdd (fun _ : Fin r ↦ T)) ≤ (r * b : ℕ) := by
  let P := TensorQ.tensorStrassen K 3 (by decide)
  letI : Nonempty (AsymptoticSpectrumPoint (TensorQ K 3) P) := mme_spectrum_nonempty P
  rw [TensorQ.tensorAsymptoticRank_eq (by decide), mme_strassen_duality]
  apply ciSup_le
  intro phi
  rw [TensorQ.toQ_bigAdd, map_sum]
  have hphi : phi (TensorQ.toQ T) ≤ (b : ℝ) :=
    (StrassenPreorder.eval_le_asymptoticRank P (TensorQ.toQ T) phi).trans
      (by rwa [← TensorQ.tensorAsymptoticRank_eq (by decide)] )
  calc
    _ ≤ ∑ _ : Fin r, (b : ℝ) := Finset.sum_le_sum (fun _ _ ↦ hphi)
    _ = _ := by simp [Nat.cast_mul]

theorem solution {K : Type u} [Field K]
    (N inputs outputs a b c : ℕ) (tau : ℝ) (hvolume : 1 ≤ a * b * c)
    (hextract : Restrict (bigAdd (fun _ : Fin outputs ↦ MMObj K a b c))
      (bigAdd (fun _ : Fin inputs ↦ (CWObj K 5).kronPow N)))
    (hsurplus : ((inputs * 7 ^ N : ℕ) : ℝ) <
      (outputs : ℝ) * (((a * b * c : ℕ) : ℝ) ^ tau)) :
    matMulExp K < 3 * tau := by
  have hCW : tensorAsymptoticRank ((CWObj K 5).kronPow N) ≤ (7 ^ N : ℕ) :=
    mme_degenerates_asymptoticRank_le
      (mme_borderRank_kronPow_le (CWObj K 5) N 7 (mme_CW_border_rank_le 5))
  have hsource := repeated_rank_bound ((CWObj K 5).kronPow N) inputs (7 ^ N) hCW
  have hMM := (mme_tensorAsymptoticRank_mono_restrict hextract).trans hsource
  have hsum := mme_asymptotic_sum_inequality
    (fun _ : Fin outputs ↦ a) (fun _ ↦ b) (fun _ ↦ c) (inputs * 7 ^ N) hMM
  have hbound : (outputs : ℝ) * (((a * b * c : ℕ) : ℝ) ^ (matMulExp_strassen K / 3)) ≤
      ((inputs * 7 ^ N : ℕ) : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
  by_contra hn
  have htau : tau ≤ matMulExp_strassen K / 3 := by
    rw [← mme_omega_eq_strassen]
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ ((a * b * c : ℕ) : ℝ) by exact_mod_cast hvolume) htau
  exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg outputs)).trans hbound)) hsurplus
