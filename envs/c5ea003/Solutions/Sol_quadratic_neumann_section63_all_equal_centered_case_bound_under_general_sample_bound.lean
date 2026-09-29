-- Prove2me | solution 1 for quadratic_neumann_section63_all_equal_centered_case_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-30T18:35:10.405006+00:00
-- url     : https://prove2.me/submissions/d9473c87-fc65-4b32-884e-e1f17533b498

import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_quadratic_neumann_all_equal_centered_as_fixed_matrix_fluctuation
import Theorems.Thm_entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a1
import Theorems.Thm_tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
import Theorems.Thm_sample_ratio_between_zero_and_one
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_smul_le_abs
    {n₁ n₂ : ℕ} (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (a • X) ≤ |a| * spectralNorm X := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (a • X)) =
        a • LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  rw [norm_smul]
  simp [Real.norm_eq_abs]

private lemma quadratic_all_equal_centered_scalar_abs_le (p : ℝ)
    (hp : 0 ≤ p) (hp_one : p ≤ 1) :
    |1 - 3 * p + 3 * p ^ 2| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · have hsq : 0 ≤ 3 * (p - (1 / 2 : ℝ)) ^ 2 := by positivity
    nlinarith
  · nlinarith

private lemma max_mul_min_cast_div
    {n₁ n₂ : ℕ} (hmin : 0 < min n₁ n₂) :
    ((n₁ : ℝ) * (n₂ : ℝ)) / ((min n₁ n₂ : ℕ) : ℝ) =
      ((max n₁ n₂ : ℕ) : ℝ) := by
  have hprod_nat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ :=
    max_mul_min n₁ n₂
  have hprod :
      ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) =
        (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hprod_nat
  have hmin_ne : ((min n₁ n₂ : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hmin)
  calc
    ((n₁ : ℝ) * (n₂ : ℝ)) / ((min n₁ n₂ : ℕ) : ℝ)
        = (((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ)) /
            ((min n₁ n₂ : ℕ) : ℝ) := by rw [hprod]
    _ = ((max n₁ n₂ : ℕ) : ℝ) := by field_simp [hmin_ne]

private lemma all_equal_centered_prefactor_kernel_eq_ratio
    {n₁ n₂ r m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hr : 0 < r) (hm : 0 < m) (μ₀ : ℝ) :
    (((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
        ((μ₀ * (r : ℝ) / ((min n₁ n₂ : ℕ) : ℝ)) ^ 2)) =
      μ₀ ^ 2 * ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ)) / (m : ℝ)) ^ 2 := by
  have hmin_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  let d : ℝ := ((min n₁ n₂ : ℕ) : ℝ)
  let nn : ℝ := (n₁ : ℝ) * (n₂ : ℝ)
  let N : ℝ := ((max n₁ n₂ : ℕ) : ℝ)
  let Mobs : ℝ := (m : ℝ)
  have hd_pos : 0 < d := by
    dsimp [d]
    exact_mod_cast hmin_nat
  have hnn_pos : 0 < nn := by
    dsimp [nn]
    positivity
  have hMobs_pos : 0 < Mobs := by
    dsimp [Mobs]
    exact_mod_cast hm
  have hnn_div_d : nn / d = N := by
    simpa [nn, d, N] using max_mul_min_cast_div (n₁ := n₁) (n₂ := n₂) hmin_nat
  have hp_inv :
      (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) = nn / Mobs := by
    dsimp [nn, Mobs]
    field_simp [hnn_pos.ne', hMobs_pos.ne']
  rw [hp_inv]
  have hrewrite : nn = N * d := by
    have h := hnn_div_d
    field_simp [hd_pos.ne'] at h
    linarith
  rw [hrewrite]
  field_simp [hd_pos.ne', hMobs_pos.ne']
  ring

private lemma all_equal_centered_sqrt_eq
    {n₁ n₂ r m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hr : 0 < r) (hm : 0 < m) (β : ℝ) :
    0 ≤ β →
    0 ≤ Real.log (((max n₁ n₂ : ℕ) : ℝ)) →
    Real.sqrt
        ((β * ((max n₁ n₂ : ℕ) : ℝ) *
            Real.log (((max n₁ n₂ : ℕ) : ℝ))) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) =
    Real.sqrt
        ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) *
          (β * Real.log (((max n₁ n₂ : ℕ) : ℝ)))) / (m : ℝ)) := by
  intro hβ hlog
  let nn : ℝ := (n₁ : ℝ) * (n₂ : ℝ)
  let N : ℝ := ((max n₁ n₂ : ℕ) : ℝ)
  let R : ℝ := (r : ℝ)
  let Mobs : ℝ := (m : ℝ)
  let logN : ℝ := Real.log N
  have hnn_pos : 0 < nn := by
    dsimp [nn]
    positivity
  have hR_pos : 0 < R := by
    dsimp [R]
    exact_mod_cast hr
  have hMobs_pos : 0 < Mobs := by
    dsimp [Mobs]
    exact_mod_cast hm
  have hlogN_nonneg : 0 ≤ logN := by
    simpa [logN, N] using hlog
  have harg1 : 0 ≤ (β * N * logN) / (Mobs / nn) := by
    positivity
  have harg2 : 0 ≤ R / nn := by positivity
  rw [← Real.sqrt_mul harg1]
  congr 1
  field_simp [hnn_pos.ne', hMobs_pos.ne']
  ring

private lemma all_equal_centered_scale_eq_first_term
    {n₁ n₂ r m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hr : 0 < r) (hm : 0 < m)
    (β μ₀ μ₁ : ℝ) (hβ : 0 ≤ β)
    (hlog : 0 ≤ Real.log (((max n₁ n₂ : ℕ) : ℝ))) :
    (((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
      (Real.sqrt
        ((β * ((max n₁ n₂ : ℕ) : ℝ) *
            Real.log (((max n₁ n₂ : ℕ) : ℝ))) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          ((μ₀ * (r : ℝ) / ((min n₁ n₂ : ℕ) : ℝ)) ^ 2)))) =
      (μ₀ ^ 2 * μ₁) *
        Real.sqrt
          ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) *
            (β * Real.log (((max n₁ n₂ : ℕ) : ℝ)))) / (m : ℝ)) *
          ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ)) / (m : ℝ)) ^ 2 := by
  have hpref :=
    all_equal_centered_prefactor_kernel_eq_ratio
      (n₁ := n₁) (n₂ := n₂) (r := r) (m := m) hn₁ hn₂ hr hm μ₀
  have hsqrt :=
    all_equal_centered_sqrt_eq
      (n₁ := n₁) (n₂ := n₂) (r := r) (m := m) hn₁ hn₂ hr hm β hβ hlog
  calc
    (((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
      (Real.sqrt
        ((β * ((max n₁ n₂ : ℕ) : ℝ) *
            Real.log (((max n₁ n₂ : ℕ) : ℝ))) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          ((μ₀ * (r : ℝ) / ((min n₁ n₂ : ℕ) : ℝ)) ^ 2))))
        =
      μ₁ *
        (Real.sqrt
          ((β * ((max n₁ n₂ : ℕ) : ℝ) *
              Real.log (((max n₁ n₂ : ℕ) : ℝ))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
          ((μ₀ * (r : ℝ) / ((min n₁ n₂ : ℕ) : ℝ)) ^ 2)) := by ring
    _ =
      μ₁ *
        Real.sqrt
          ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) *
            (β * Real.log (((max n₁ n₂ : ℕ) : ℝ)))) / (m : ℝ)) *
        (μ₀ ^ 2 * ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ)) / (m : ℝ)) ^ 2) := by
      rw [hsqrt, hpref]
    _ =
      (μ₀ ^ 2 * μ₁) *
        Real.sqrt
          ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) *
            (β * Real.log (((max n₁ n₂ : ℕ) : ℝ)))) / (m : ℝ)) *
          ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ)) / (m : ℝ)) ^ 2 := by ring

private lemma general_sample_bound_implies_fixed_matrix_sample_lower
    {C' β μ₀ μ₁ : ℝ} {n₁ n₂ r m : ℕ}
    (hC' : 1 ≤ C') (hβ : 2 < β)
    (hn₁ : 0 < n₁) (hr : 0 < r)
    (hμ₁ : 1 ≤ μ₁)
    (hmLower :
      (m : ℝ) ≥
        C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
          * (↑(max n₁ n₂)) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂)))) :
    (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
  let K : ℝ :=
    max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
      (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
  let N : ℝ := (↑(max n₁ n₂) : ℝ)
  let R : ℝ := (r : ℝ)
  let L : ℝ := β * Real.log N
  have hN_nat : 0 < max n₁ n₂ :=
    lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_one : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hlog_nonneg : 0 ≤ Real.log N := Real.log_nonneg hN_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hR_one : 1 ≤ R := by
    dsimp [R]
    exact_mod_cast (Nat.succ_le_of_lt hr)
  have hK_one : 1 ≤ K := by
    have hμ₁sq : 1 ≤ μ₁ ^ 2 := by nlinarith [hμ₁]
    exact le_trans hμ₁sq (by dsimp [K]; exact le_trans (le_max_left _ _) (le_max_left _ _))
  have hprod :
      L * N ≤ C' * K * N * R * L := by
    calc
      L * N = (1 * 1 * N * 1 * L) := by ring
      _ ≤ C' * K * N * R * L := by
        gcongr
  have hmLower' : (m : ℝ) ≥ C' * K * N * R * L := by
    simpa [K, N, R, L, mul_assoc] using hmLower
  calc
    β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))
        = L * N := by simp [L, N, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ C' * K * N * R * L := hprod
    _ ≤ (m : ℝ) := hmLower'

private lemma all_equal_base_entry_bound_a1
    (Cker : ℝ) (hCker : 0 < Cker) :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ μ₁ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r →
      1 ≤ μ₀ → 1 ≤ μ₁ →
      A0 S μ₀ → A1 S μ₁ →
      (∀ i j,
        |tangentCoordinateKernel S i j i j| ≤
          Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) →
      entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) ≤
        Cker ^ 2 *
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)) := by
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 hkernel
  let signBound : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
  let kernelBound : ℝ := Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))
  have hsign_nonneg : 0 ≤ signBound := by
    dsimp [signBound]
    positivity
  have hkernel_nonneg : 0 ≤ kernelBound := by
    dsimp [kernelBound]
    positivity
  have hsign :
      entrySupNorm (signMatrix S) ≤ signBound := by
    simpa [signBound] using entry_sup_norm_sign_matrix_bound_from_a1 hn₁ hn₂ μ₁ S hA1
  have hbase :=
    entry_sup_norm_quadratic_all_equal_base_bound_from_sign_and_kernel_bounds
      hn₁ hn₂ S hsign_nonneg hkernel_nonneg hsign (by simpa [kernelBound] using hkernel)
  calc
    entrySupNorm (quadraticNeumannAllEqualBaseMatrix S)
        ≤ signBound * kernelBound ^ 2 := hbase
    _ = Cker ^ 2 *
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)) := by
        simp [signBound, kernelBound]
        ring

private lemma all_equal_centered_pointwise_bound
    (Cfixed Cker C : ℝ) :
    0 < Cfixed → 0 < Cker → Cfixed * Cker ^ 2 ≤ C →
    ∀ (β : ℝ), 2 < β →
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ μ₁ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
      1 ≤ μ₀ → 1 ≤ μ₁ →
      A0 S μ₀ → A1 S μ₁ →
      (∀ i j,
        |tangentCoordinateKernel S i j i j| ≤
          Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) →
      ∀ Omega,
      CenteredSamplingSpectralBound Omega
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (quadraticNeumannAllEqualBaseMatrix S)
          (Cfixed * Real.sqrt
            ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm (quadraticNeumannAllEqualBaseMatrix S)) →
      spectralNorm
          (quadraticNeumannAllEqualCenteredContribution Omega S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
        (let N : ℝ := ↑(max n₁ n₂)
         let R : ℝ := (r : ℝ)
         let Mobs : ℝ := (m : ℝ)
         let logN : ℝ := Real.log N
         C *
           ((μ₀ ^ 2 * μ₁) *
              Real.sqrt ((N * R * (β * logN)) / Mobs) *
                ((N * R) / Mobs) ^ 2 +
            μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
            Real.sqrt (β * logN) *
                Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                  (μ₀ ^ 2 * R) +
            Real.rpow
              ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
              ((3 : ℝ) / 2))) := by
  intro hCfixed hCker hCscale β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hkernel Omega hCentered
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let N : ℝ := ((max n₁ n₂ : ℕ) : ℝ)
  let R : ℝ := (r : ℝ)
  let Mobs : ℝ := (m : ℝ)
  let logN : ℝ := Real.log N
  let term₁ : ℝ :=
    (μ₀ ^ 2 * μ₁) * Real.sqrt ((N * R * (β * logN)) / Mobs) *
      ((N * R) / Mobs) ^ 2
  let term₂ : ℝ := μ₀ ^ 2 * ((N * R) / Mobs) ^ 2
  let term₃ : ℝ :=
    Real.sqrt (β * logN) *
      Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)
  let term₄ : ℝ :=
    Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2)
  let Φ : ℝ := term₁ + term₂ + term₃ + term₄
  have hratio := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hN_nat : 0 < max n₁ n₂ :=
    lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_one : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hlog_nonneg : 0 ≤ logN := by
    dsimp [logN]
    exact Real.log_nonneg hN_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hR_pos : 0 < R := by
    dsimp [R]
    exact_mod_cast hr
  by_cases hmzero : m = 0
  · subst m
    have hzero_bound :
        spectralNorm
            (quadraticNeumannAllEqualCenteredContribution Omega S
              ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤ 0 := by
      have hp0 : ((0 : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) = 0 := by simp
      rw [hp0, quadratic_neumann_all_equal_centered_as_fixed_matrix_fluctuation Omega S 0]
      simpa using
        spectralNorm_smul_le_abs (0 : ℝ)
          (centeredSamplingFluctuation Omega 0 (quadraticNeumannAllEqualBaseMatrix S))
    simpa [N, R, Mobs, logN] using hzero_bound
  · have hm_pos_nat : 0 < m := Nat.pos_of_ne_zero hmzero
    have hMobs_pos : 0 < Mobs := by
      dsimp [Mobs]
      exact_mod_cast hm_pos_nat
    have hbase :=
      all_equal_base_entry_bound_a1 Cker hCker n₁ n₂ r M μ₀ μ₁ S
        hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 hkernel
    have hcentered' :
        spectralNorm (centeredSamplingFluctuation Omega p
            (quadraticNeumannAllEqualBaseMatrix S)) ≤
          Cfixed * Real.sqrt
            ((β * N * logN) / p) *
            entrySupNorm (quadraticNeumannAllEqualBaseMatrix S) := by
      simpa [p, N, logN, CenteredSamplingSpectralBound, mul_assoc] using hCentered
    let a : ℝ := (p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2)
    have hcoeff :
        |a| ≤ (p⁻¹) ^ 2 := by
      have hscalar := quadratic_all_equal_centered_scalar_abs_le p hratio.1 hratio.2
      have hinv_sq_nonneg : 0 ≤ (p⁻¹) ^ 2 := sq_nonneg _
      calc
        |a| = (p⁻¹) ^ 2 * |1 - 3 * p + 3 * p ^ 2| := by
          simp [a, abs_mul]
        _ ≤ (p⁻¹) ^ 2 * 1 := mul_le_mul_of_nonneg_left hscalar hinv_sq_nonneg
        _ = (p⁻¹) ^ 2 := by ring
    have hQ :
        spectralNorm
            (quadraticNeumannAllEqualCenteredContribution Omega S p) ≤
          (Cfixed * Cker ^ 2) * term₁ := by
      rw [quadratic_neumann_all_equal_centered_as_fixed_matrix_fluctuation Omega S p]
      have hsmul :
          spectralNorm
              (a • centeredSamplingFluctuation Omega p
                (quadraticNeumannAllEqualBaseMatrix S)) ≤
            |a| *
              spectralNorm
                (centeredSamplingFluctuation Omega p
                  (quadraticNeumannAllEqualBaseMatrix S)) :=
        spectralNorm_smul_le_abs a
          (centeredSamplingFluctuation Omega p (quadraticNeumannAllEqualBaseMatrix S))
      have hstep1 :
          |a| *
              spectralNorm
                (centeredSamplingFluctuation Omega p
                  (quadraticNeumannAllEqualBaseMatrix S)) ≤
            (p⁻¹) ^ 2 *
              (Cfixed * Real.sqrt ((β * N * logN) / p) *
                entrySupNorm (quadraticNeumannAllEqualBaseMatrix S)) := by
        exact mul_le_mul hcoeff hcentered' (norm_nonneg _) (sq_nonneg _)
      have hstep2 :
          (p⁻¹) ^ 2 *
              (Cfixed * Real.sqrt ((β * N * logN) / p) *
                entrySupNorm (quadraticNeumannAllEqualBaseMatrix S)) ≤
            (p⁻¹) ^ 2 *
              (Cfixed * Real.sqrt ((β * N * logN) / p) *
                (Cker ^ 2 *
                  (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)))) := by
        have hleft_nonneg :
            0 ≤ (p⁻¹) ^ 2 := sq_nonneg _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbase
            (mul_nonneg (le_of_lt hCfixed) (Real.sqrt_nonneg _)))
          hleft_nonneg
      have hscale :
          (p⁻¹) ^ 2 *
              (Cfixed * Real.sqrt ((β * N * logN) / p) *
                (Cker ^ 2 *
                  (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)))) =
            (Cfixed * Cker ^ 2) * term₁ := by
        have hscale0 :=
          all_equal_centered_scale_eq_first_term
            (n₁ := n₁) (n₂ := n₂) (r := r) (m := m)
            hn₁ hn₂ hr hm_pos_nat β μ₀ μ₁ hβ_nonneg
            (by simpa [N, logN] using hlog_nonneg)
        calc
          (p⁻¹) ^ 2 *
              (Cfixed * Real.sqrt ((β * N * logN) / p) *
                (Cker ^ 2 *
                  (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2))))
              =
            (Cfixed * Cker ^ 2) *
              (((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2) *
                (Real.sqrt
                  ((β * ((max n₁ n₂ : ℕ) : ℝ) *
                      Real.log (((max n₁ n₂ : ℕ) : ℝ))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    ((μ₀ * (r : ℝ) / ((min n₁ n₂ : ℕ) : ℝ)) ^ 2)))) := by
                simp [p, N, logN]
                ring
          _ =
            (Cfixed * Cker ^ 2) *
              ((μ₀ ^ 2 * μ₁) *
                Real.sqrt
                  ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) *
                    (β * Real.log (((max n₁ n₂ : ℕ) : ℝ)))) / (m : ℝ)) *
                  ((((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ)) / (m : ℝ)) ^ 2) := by
                rw [hscale0]
          _ = (Cfixed * Cker ^ 2) * term₁ := by
                simp [term₁, N, R, Mobs, logN]
      calc
        spectralNorm
            (a • centeredSamplingFluctuation Omega p
              (quadraticNeumannAllEqualBaseMatrix S)) ≤
          |a| *
            spectralNorm
              (centeredSamplingFluctuation Omega p
                (quadraticNeumannAllEqualBaseMatrix S)) := hsmul
        _ ≤
          (p⁻¹) ^ 2 *
            (Cfixed * Real.sqrt ((β * N * logN) / p) *
              entrySupNorm (quadraticNeumannAllEqualBaseMatrix S)) := hstep1
        _ ≤
          (p⁻¹) ^ 2 *
            (Cfixed * Real.sqrt ((β * N * logN) / p) *
              (Cker ^ 2 *
                (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  ((μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2)))) := hstep2
        _ = (Cfixed * Cker ^ 2) * term₁ := hscale
    have hterm₁_nonneg : 0 ≤ term₁ := by
      dsimp [term₁, N, R, Mobs, logN]
      positivity
    have hterm₂_nonneg : 0 ≤ term₂ := by
      dsimp [term₂, N, R, Mobs]
      positivity
    have hterm₃_nonneg : 0 ≤ term₃ := by
      dsimp [term₃, N, R, Mobs, logN]
      positivity
    have hterm₄_nonneg : 0 ≤ term₄ := by
      dsimp [term₄, N, R, Mobs, logN]
      apply Real.rpow_nonneg
      positivity
    have hscale_le : (Cfixed * Cker ^ 2) * term₁ ≤ C * term₁ := by
      exact mul_le_mul_of_nonneg_right hCscale hterm₁_nonneg
    have hterm₁_le_Φ : term₁ ≤ Φ := by
      dsimp [Φ]
      nlinarith
    have hC_nonneg : 0 ≤ C := le_trans (by positivity : 0 ≤ Cfixed * Cker ^ 2) hCscale
    have hCterm₁_le : C * term₁ ≤ C * Φ :=
      mul_le_mul_of_nonneg_left hterm₁_le_Φ hC_nonneg
    calc
      spectralNorm
          (quadraticNeumannAllEqualCenteredContribution Omega S p) ≤
        (Cfixed * Cker ^ 2) * term₁ := hQ
      _ ≤ C * term₁ := hscale_le
      _ ≤ C * Φ := hCterm₁_le
      _ =
        (let N : ℝ := ↑(max n₁ n₂)
         let R : ℝ := (r : ℝ)
         let Mobs : ℝ := (m : ℝ)
         let logN : ℝ := Real.log N
         C *
           ((μ₀ ^ 2 * μ₁) *
              Real.sqrt ((N * R * (β * logN)) / Mobs) *
                ((N * R) / Mobs) ^ 2 +
            μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
            Real.sqrt (β * logN) *
                Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                  (μ₀ ^ 2 * R) +
            Real.rpow
              ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
              ((3 : ℝ) / 2))) := by
          rfl

theorem solution :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (quadraticNeumannAllEqualCenteredContribution Omega S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 C *
                   ((μ₀ ^ 2 * μ₁) *
                      Real.sqrt ((N * R * (β * logN)) / Mobs) *
                        ((N * R) / Mobs) ^ 2 +
                    μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                    Real.sqrt (β * logN) *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          (μ₀ ^ 2 * R) +
                    Real.rpow
                      ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                      ((3 : ℝ) / 2)))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with
    ⟨Cfixed, hCfixed, hFixed⟩
  rcases tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim with
    ⟨Cker, hCker, hKernel⟩
  let C : ℝ := max 1 (Cfixed * Cker ^ 2)
  refine ⟨C, 1, ?_, zero_lt_one, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hC'_one : (1 : ℝ) ≤ C' :=
    le_trans (le_max_left (1 : ℝ) (Cfixed * Cker ^ 2)) hC'
  have hCscale : Cfixed * Cker ^ 2 ≤ C :=
    le_max_right (1 : ℝ) (Cfixed * Cker ^ 2)
  have hFixedSample :
      (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    general_sample_bound_implies_fixed_matrix_sample_lower
      hC'_one hβ hn₁ hr hμ₁ hmLower
  have hFixedProb :=
    hFixed β hβ n₁ n₂ m (quadraticNeumannAllEqualBaseMatrix S)
      hn₁ hn₂ hm hFixedSample
  have hratio := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            CenteredSamplingSpectralBound Omega p
              (quadraticNeumannAllEqualBaseMatrix S)
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) *
                    Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm (quadraticNeumannAllEqualBaseMatrix S))) ≤
        bernoulliEventProb p
          (fun Omega =>
            spectralNorm
              (quadraticNeumannAllEqualCenteredContribution Omega S p) ≤
              (let N : ℝ := ↑(max n₁ n₂)
               let R : ℝ := (r : ℝ)
               let Mobs : ℝ := (m : ℝ)
               let logN : ℝ := Real.log N
               C *
                 ((μ₀ ^ 2 * μ₁) *
                    Real.sqrt ((N * R * (β * logN)) / Mobs) *
                      ((N * R) / Mobs) ^ 2 +
                  μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 +
                  Real.sqrt (β * logN) *
                      Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                        (μ₀ ^ 2 * R) +
                  Real.rpow
                    ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs)
                    ((3 : ℝ) / 2)))) :=
    bernoulli_event_probability_mono p _ _ hratio.1 hratio.2
      (by
        intro Omega hGood
        exact
          all_equal_centered_pointwise_bound Cfixed Cker C hCfixed hCker hCscale
            β hβ n₁ n₂ r m M μ₀ μ₁ S
            hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
            (hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0)
            Omega hGood)
  simpa [p] using le_trans hFixedProb hMono
