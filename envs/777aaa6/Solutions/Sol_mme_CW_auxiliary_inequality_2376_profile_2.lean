-- Prove2me | solution 2 for mme_CW_auxiliary_inequality_2376_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:16:48.480364+00:00
-- url     : https://prove2.me/submissions/7da18111-c908-40c7-88f6-5eeeac29e23f

import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_CW_square_laser_value_below_2376_of_coupled_below
import Theorems.Thm_mme_CW_square_asymptoticRank_le
import Theorems.Thm_mme_tau_value_below_base_le_of_asymptoticRank_le

open MME

universe u

/-!
Sound replacement reduction for the exact auxiliary upper bound.

The laser theorem supplies every value strictly below the auxiliary
exponential rate.  If that rate were above 64, its midpoint with 64 would be
an attained tau-value above 64, contradicting the square rank bound.
-/

theorem solution
    {K : Type u} [Field K]
    (homega : 2 ≤ matMulExp_strassen K) :
    auxiliaryRHS 6 (matMulExp_strassen K / 3)
        cw2376_a cw2376_b cw2376_c cw2376_d ≤ 64 := by
  let tau : ℝ := matMulExp_strassen K / 3
  let A : ℝ := auxiliaryRHS 6 tau
    cw2376_a cw2376_b cw2376_c cw2376_d
  have htau : 2 ≤ 3 * tau := by
    dsimp [tau]
    linarith
  have hcoupled :
      ∀ Vc : ℝ, 0 ≤ Vc →
        Vc < 4 * (6 : ℝ) ^ (3 * tau) *
          ((6 : ℝ) ^ (3 * tau) + 2) →
        HasTauValueAtLeast
          (cyclicSymmetrization (coupledObj K 6)) tau Vc := by
    intro Vc hVc hVc_lt
    exact mme_CW_q6_coupled_raw_cyclic_value_below
      (K := K) tau htau Vc hVc hVc_lt
  change A ≤ 64
  have hrank :
      tensorAsymptoticRank
          (TensorObj.kron (CWObj K 6) (CWObj K 6)) ≤ (64 : ℝ) := by
    have h := mme_CW_square_asymptoticRank_le (K := K) 6
    norm_num at h ⊢
    exact h
  apply mme_tau_value_below_base_le_of_asymptoticRank_le
    (K := K) (T := TensorObj.kron (CWObj K 6) (CWObj K 6))
    (B := A) (R := 64) (by norm_num) hrank
  intro V hV_one hV_lt
  have hvalue :=
    mme_CW_square_laser_value_below_2376_of_coupled_below
      (K := K) tau htau hcoupled V (by linarith) hV_lt
  simpa [tau] using hvalue
