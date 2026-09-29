-- Prove2me | solution 1 for mme_CW_q6_coupled_even_power_finite_extractions_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T06:13:44.432992+00:00
-- url     : https://prove2.me/submissions/322dcdde-024c-4002-ab1a-9f2e57e111f0

import Theorems.Thm_mme_CW_q6_primary_hash_family_Ctensor_certificates
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_bounded
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
import Mathlib.Tactic

open MME BigOperators Filter
universe u
set_option autoImplicit false

private theorem behrend_loss_bound (N H : ℕ) (hH : H ≤ 4 ^ N) :
    Real.exp (-200 * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))) := by
  have hp : H + 1 ≤ 4 ^ (N + 1) := by
    have hpos : 0 < 4 ^ N := by positivity
    rw [pow_succ]
    omega
  have hlog : Real.log ((H + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
      (show ((H + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) by exact_mod_cast hp)
    rw [Real.log_pow] at h
    have hfour : Real.log (4 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log 4 := h
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := mul_comm _ _
  have hl0 : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hs : Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hl0,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity),
      Real.sqrt_nonneg (Real.log ((H + 1 : ℕ) : ℝ)),
      Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  apply Real.exp_le_exp.mpr
  linarith


theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
          (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^ (2 * N) *
              Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  classical
  obtain ⟨C, hC, hcap⟩ := mme_CW_q6_primary_hash_sqrt_capacity_bounded tau htau
  refine ⟨C + 200, by linarith, ?_⟩
  filter_upwards [hcap] with N hcap
  let L : ℕ := ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
  let G : ℕ := N - L
  dsimp only at hcap
  obtain ⟨A, H, family, hHbound, hcap⟩ := hcap
  obtain ⟨cert⟩ := mme_CW_q6_primary_hash_family_Ctensor_certificates
    (K := K) N _ _ A H family
  obtain ⟨k, a, b, c, hr, hk, hv⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction cert family.hHpos
  refine ⟨k, a, b, c, hr.trans
    (mme_cyclicSymmetrization_kronPow_isomorphic (coupledObj K 6) (2 * N)).2, ?_⟩
  have hside (G L : ℕ) : 36 ^ (2 * G) * 6 ^ (2 * L) = 6 ^ (4 * G + 2 * L) := by
    calc
      _ = (6 ^ 2) ^ (2 * G) * 6 ^ (2 * L) := by norm_num
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  have hcube (x : ℕ) : x * x * x = x ^ 3 := by ring
  simp only [hside, hcube] at hcap
  have hloss := behrend_loss_bound N H hHbound
  have hcount : (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
      Real.exp (-200 * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
    calc
      _ ≤ (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hloss (by positivity)
      _ ≤ _ := by simpa only [mul_assoc] using hk
  let w : ℝ := (((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau
  have hweighted := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ w from Real.rpow_nonneg (by positivity) tau)
  have hsum : (∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) = (k : ℝ) * w := by
    simp only [hv]
    simp [w, G, L]
  let raw : ℝ := 4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let x : ℝ := Real.sqrt ((N + 1 : ℕ) : ℝ)
  change raw ^ (2 * N) * Real.exp (-C * x) ≤
    ((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2 * w at hcap
  rw [hsum]
  change raw ^ (2 * N) * Real.exp (-(C + 200) * x) ≤ (k : ℝ) * w
  calc
    _ = (raw ^ (2 * N) * Real.exp (-C * x)) * Real.exp (-200 * x) := by
      rw [show -(C + 200) * x = -C * x + -200 * x by ring, Real.exp_add]
      ring
    _ ≤ (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2 * w) * Real.exp (-200 * x) :=
      mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
    _ ≤ _ := by
      simpa only [x, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hweighted

#print axioms solution
