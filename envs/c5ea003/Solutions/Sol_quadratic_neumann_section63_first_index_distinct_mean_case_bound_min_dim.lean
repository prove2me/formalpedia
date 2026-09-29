-- Prove2me | solution 1 for quadratic_neumann_section63_first_index_distinct_mean_case_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T10:35:46.92598+00:00
-- url     : https://prove2.me/submissions/e6c2516a-d986-423a-a633-4eb4a6991712

import Theorems.Thm_fixed_matrix_centered_sampling_spectral_bound
import Theorems.Thm_quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_min_dim
import Theorems.Thm_quadratic_neumann_first_index_distinct_mean_as_coefficient_fluctuation
import Theorems.Thm_bernoulli_event_probability_mono
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option maxHeartbeats 3200000

open MatrixCompletion

/-!
Source: Candès–Recht 2008, Section 6.3, PDF pp. 31--32, the mean part `S₂` of the
`ω₁ ≠ ω₂ = ω₃` case, controlled by Theorem 6.3 applied to the deterministic
Lemma-6.8 coefficient matrix `H` in the **honest rectangular `min(n₁,n₂)` scale**.

The mean contribution equals `(1-p)·(P_Ω-pI)/p (H)` where
`H = quadraticFirstIndexDistinctMeanCoefficientMatrix S p`.  Theorem 6.3
(`021320e3`) gives `spectralNorm(fluct H) ≤ Cfixed·√(βN logN/p)·entrySup H`, and
the honest Lemma-6.8 (eq. 6.22) rectangular entry bound
(`..._mean_coefficient_entry_bound_min_dim`, the corrected `r/min` node)

  `entrySup H ≤ C68·p⁻¹·(μ₀ r/min)·(μ₁√(r/nn) + μ₀ r/min)`

splits into a sign-envelope term `Ba` and the `Λ_U E Λ_V` cross-term `Bb`.  Fed
through Theorem 6.3, `Ba` lands in `Φ`'s fourth term `t₄` (`Ba/t₄ ≤ 1`) and `Bb`
lands **exactly** in the new `(N/min)`-aware term `t₅` (`Bb/t₅ = 1`).  Hence the
honest bound closes the mean case at the corrected scale `Φ + t₅`, with NO
thin-matrix blow-up (the fatal defect of the `N`-only `Φ`).  This routes ONLY
through the corrected `r/min` node, NOT through any false `r/max`/`r/N` stub.
-/

-- spectralNorm helpers --------------------------------------------------------

private theorem spectralNorm_nonneg {n1 n2 : Nat} (A : RealMatrix n1 n2) :
    0 ≤ spectralNorm A := norm_nonneg _

private theorem spectralNorm_smul {n1 n2 : Nat} (c : ℝ) (A : RealMatrix n1 n2) :
    spectralNorm (c • A) = |c| * spectralNorm A := by
  unfold spectralNorm
  rw [show Matrix.toEuclideanLin (c • A) = c • (Matrix.toEuclideanLin A) from map_smul _ _ _]
  rw [show LinearMap.toContinuousLinearMap (c • (Matrix.toEuclideanLin A))
      = c • (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) from map_smul _ _ _]
  rw [norm_smul]; simp [Real.norm_eq_abs]

-- general-sample-bound → βNlogN fixed-matrix lower bound -----------------------

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
    dsimp [N]; exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hlog_nonneg : 0 ≤ Real.log N := Real.log_nonneg hN_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hL_nonneg : 0 ≤ L := by dsimp [L]; positivity
  have hR_one : 1 ≤ R := by dsimp [R]; exact_mod_cast (Nat.succ_le_of_lt hr)
  have hK_one : 1 ≤ K := by
    have hμ₁sq : 1 ≤ μ₁ ^ 2 := by nlinarith [hμ₁]
    exact le_trans hμ₁sq
      (by dsimp [K]; exact le_trans (le_max_left _ _) (le_max_left _ _))
  have hprod : L * N ≤ C' * K * N * R * L := by
    calc
      L * N = (1 * 1 * N * 1 * L) := by ring
      _ ≤ C' * K * N * R * L := by gcongr
  have hmLower' : (m : ℝ) ≥ C' * K * N * R * L := by
    simpa [K, N, R, L, mul_assoc] using hmLower
  calc
    β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))
        = L * N := by simp [L, N, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ C' * K * N * R * L := hprod
    _ ≤ (m : ℝ) := hmLower'

-- (n₁ : ℝ)*(n₂ : ℝ) = max·min --------------------------------------------------

private lemma prod_eq_max_mul_min (n₁ n₂ : ℕ) :
    ((n₁ : ℝ) * (n₂ : ℝ)) = ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) := by
  have hprod_nat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ := max_mul_min n₁ n₂
  have : ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hprod_nat
  linarith [this]

-- Core arithmetic bridge: honest r/min coefficient rate ≤ t₄ + t₅ --------------
-- The honest Theorem-6.3 spectral rate for `H` is
--   √(N·βL/p)·p⁻¹·B·(sq + B),   B = μ₀·R/mn,  sq = μ₁·√(R/nn),  nn = N·mn, mn ≤ N.
-- We prove this is ≤ t₄ + t₅ where
--   t₄ = ((μ₀ μ₁ N R βL)/M)^{3/2},
--   t₅ = √(βL)·μ₀²·((N R)/M)^{3/2}·√((N R)/mn).
-- Split: √(N βL/p) p⁻¹ B sq ≤ t₄   and   √(N βL/p) p⁻¹ B² ≤ t₅.

-- Ba part: √(N βL/p)·p⁻¹·B·sq ≤ t₄ .  With p = M/nn, nn = N mn:
--   LHS² = N βL (nn/M) (nn/M)² (μ₀ R/mn)² (μ₁² R/nn)
--        = βL μ₀² μ₁² R³ N nn² /(M³ mn²) ... and t₄² = (μ₀ μ₁ N R βL/M)³.
-- t₄² / LHS² = (μ₀ μ₁ βL) · (N/mn... ) — we prove LHS² ≤ t₄² directly.
private lemma Ba_le_term4
    (μ₀ μ₁ N R βL p nn mn M : ℝ)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hN : 0 < N) (hR : 1 ≤ R) (hM : 0 < M) (hmn : 0 < mn)
    (hmnN : mn ≤ N) (hβL : 1 ≤ βL) (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁) :
    Real.sqrt (N * βL / p) * p⁻¹ * (μ₀ * R / mn) * (μ₁ * Real.sqrt (R / nn)) ≤
      Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3 : ℝ) / 2) := by
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hβL0 : 0 < βL := lt_of_lt_of_le one_pos hβL
  set Q : ℝ :=
    Real.sqrt (N * βL / p) * p⁻¹ * (μ₀ * R / mn) * (μ₁ * Real.sqrt (R / nn)) with hQ
  set T : ℝ := Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3 : ℝ) / 2) with hT
  have hbaseT_pos : 0 < (μ₀ * μ₁ * N * R * βL) / M := by positivity
  have hQnn : 0 ≤ Q := by
    rw [hQ]; positivity
  have hTnn : 0 ≤ T := by rw [hT]; exact Real.rpow_nonneg (le_of_lt hbaseT_pos) _
  have hsqrt_p : Real.sqrt (N * βL / p) ^ 2 = N * βL / p := Real.sq_sqrt (by positivity)
  have hsqrt_nn : Real.sqrt (R / nn) ^ 2 = R / nn := Real.sq_sqrt (by positivity)
  have hrpow_sq :
      (Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3 : ℝ) / 2)) ^ 2
        = ((μ₀ * μ₁ * N * R * βL) / M) ^ 3 := by
    have h1 : (Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3:ℝ)/2)) ^ (2:ℕ)
        = (Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3:ℝ)/2)).rpow ((2:ℕ):ℝ) :=
      (Real.rpow_natCast _ 2).symm
    have h2 : (Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) ((3:ℝ)/2)).rpow ((2:ℕ):ℝ)
        = Real.rpow ((μ₀ * μ₁ * N * R * βL) / M) (((3:ℝ)/2) * ((2:ℕ):ℝ)) :=
      (Real.rpow_mul (le_of_lt hbaseT_pos) _ _).symm
    rw [h1, h2, show ((3:ℝ)/2) * ((2:ℕ):ℝ) = ((3:ℕ):ℝ) by norm_num]
    exact Real.rpow_natCast _ 3
  have hMne : M ≠ 0 := ne_of_gt hM
  have hNne : N ≠ 0 := ne_of_gt hN
  have hmnne : mn ≠ 0 := ne_of_gt hmn
  have hnnne : nn ≠ 0 := ne_of_gt hnn_pos
  -- Q² = βL·μ₀²·μ₁²·R³·N·nn²/(M³·mn²·... ) : compute symbolically
  have hQsq :
      Q ^ 2 = (N * βL / p) * (p⁻¹) ^ 2 * (μ₀ * R / mn) ^ 2 * (μ₁ ^ 2 * (R / nn)) := by
    have hstep : Q ^ 2 = (Real.sqrt (N * βL / p)) ^ 2 * (p⁻¹) ^ 2
        * (μ₀ * R / mn) ^ 2 * (μ₁ ^ 2 * (Real.sqrt (R / nn)) ^ 2) := by
      rw [hQ]; ring
    rw [hstep, hsqrt_p, hsqrt_nn]
  -- substitute p and nn to get a clean rational form
  have hQsq' :
      Q ^ 2 = βL * μ₀ ^ 2 * μ₁ ^ 2 * R ^ 3 * N ^ 3 / M ^ 3 := by
    rw [hQsq, hp, hnn]
    field_simp
    try ring
  have hTsq :
      T ^ 2 = μ₀ ^ 3 * μ₁ ^ 3 * N ^ 3 * R ^ 3 * βL ^ 3 / M ^ 3 := by
    rw [hT, hrpow_sq]
    field_simp
    try ring
  have hQsq_le_Tsq : Q ^ 2 ≤ T ^ 2 := by
    rw [hQsq', hTsq]
    -- βL μ₀² μ₁² R³ N³ ≤ μ₀³ μ₁³ N³ R³ βL³ , i.e. need 1 ≤ βL² μ₀ μ₁
    have hbig : μ₀ ^ 2 * μ₁ ^ 2 * βL ≤ μ₀ ^ 3 * μ₁ ^ 3 * βL ^ 3 := by
      have h1 : μ₀ ^ 2 ≤ μ₀ ^ 3 := by nlinarith [hμ₀, hμ₀0]
      have h2 : μ₁ ^ 2 ≤ μ₁ ^ 3 := by nlinarith [hμ₁, hμ₁0]
      have h5 : βL ≤ βL ^ 3 := by nlinarith [hβL, hβL0, sq_nonneg (βL - 1), mul_pos hβL0 hβL0]
      gcongr
    have hnum :
        βL * μ₀ ^ 2 * μ₁ ^ 2 * R ^ 3 * N ^ 3 ≤ μ₀ ^ 3 * μ₁ ^ 3 * N ^ 3 * R ^ 3 * βL ^ 3 := by
      have := mul_le_mul_of_nonneg_left hbig (by positivity : (0:ℝ) ≤ N ^ 3 * R ^ 3)
      nlinarith [this]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  nlinarith [hQsq_le_Tsq, hQnn, hTnn, sq_nonneg (T - Q)]

-- Bb part: √(N βL/p)·p⁻¹·B² ≤ t₅   with equality up to the base; B = μ₀ R/mn.
--   LHS² = N βL (nn/M)³ μ₀⁴ R⁴/mn⁴,  nn = N mn ⇒ = βL μ₀⁴ R⁴ N⁴ /(M³ mn).
--   t₅² = βL μ₀⁴ ((NR)/M)³ (NR/mn) = βL μ₀⁴ N⁴ R⁴/(M³ mn).  ⇒ LHS² = t₅². Equality.
private lemma Bb_le_term5
    (μ₀ N R βL p nn mn M : ℝ)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hN : 0 < N) (hR : 1 ≤ R) (hM : 0 < M) (hmn : 0 < mn)
    (hβL : 1 ≤ βL) (hμ₀ : 1 ≤ μ₀) :
    Real.sqrt (N * βL / p) * p⁻¹ * (μ₀ * R / mn) ^ 2 ≤
      Real.sqrt βL * μ₀ ^ 2 *
        Real.rpow ((N * R) / M) ((3 : ℝ) / 2) *
          Real.sqrt ((N * R) / mn) := by
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hβL0 : 0 < βL := lt_of_lt_of_le one_pos hβL
  set Q : ℝ := Real.sqrt (N * βL / p) * p⁻¹ * (μ₀ * R / mn) ^ 2 with hQ
  set T : ℝ :=
    Real.sqrt βL * μ₀ ^ 2 * Real.rpow ((N * R) / M) ((3 : ℝ) / 2) *
      Real.sqrt ((N * R) / mn) with hT
  have hbaseM_pos : 0 < (N * R) / M := by positivity
  have hbaseNRmn_pos : 0 < (N * R) / mn := by positivity
  have hQnn : 0 ≤ Q := by rw [hQ]; positivity
  have hTnn : 0 ≤ T := by
    rw [hT]
    have := Real.rpow_nonneg (le_of_lt hbaseM_pos) ((3:ℝ)/2)
    positivity
  have hsqrt_p : Real.sqrt (N * βL / p) ^ 2 = N * βL / p := Real.sq_sqrt (by positivity)
  have hsqrt_βL : Real.sqrt βL ^ 2 = βL := Real.sq_sqrt (le_of_lt hβL0)
  have hsqrt_NRmn : Real.sqrt ((N * R) / mn) ^ 2 = (N * R) / mn :=
    Real.sq_sqrt (le_of_lt hbaseNRmn_pos)
  have hrpow_sq : (Real.rpow ((N * R) / M) ((3 : ℝ) / 2)) ^ 2 = ((N * R) / M) ^ 3 := by
    have h1 : (Real.rpow ((N * R) / M) ((3:ℝ)/2)) ^ (2:ℕ)
        = (Real.rpow ((N * R) / M) ((3:ℝ)/2)).rpow ((2:ℕ):ℝ) :=
      (Real.rpow_natCast _ 2).symm
    have h2 : (Real.rpow ((N * R) / M) ((3:ℝ)/2)).rpow ((2:ℕ):ℝ)
        = Real.rpow ((N * R) / M) (((3:ℝ)/2) * ((2:ℕ):ℝ)) :=
      (Real.rpow_mul (le_of_lt hbaseM_pos) _ _).symm
    rw [h1, h2, show ((3:ℝ)/2) * ((2:ℕ):ℝ) = ((3:ℕ):ℝ) by norm_num]
    exact Real.rpow_natCast _ 3
  have hMne : M ≠ 0 := ne_of_gt hM
  have hNne : N ≠ 0 := ne_of_gt hN
  have hmnne : mn ≠ 0 := ne_of_gt hmn
  have hQsq :
      Q ^ 2 = (N * βL / p) * (p⁻¹) ^ 2 * ((μ₀ * R / mn) ^ 2) ^ 2 := by
    have hstep : Q ^ 2 = (Real.sqrt (N * βL / p)) ^ 2 * (p⁻¹) ^ 2
        * ((μ₀ * R / mn) ^ 2) ^ 2 := by rw [hQ]; ring
    rw [hstep, hsqrt_p]
  have hQsq' : Q ^ 2 = βL * μ₀ ^ 4 * R ^ 4 * N ^ 4 / (M ^ 3 * mn) := by
    rw [hQsq, hp, hnn]
    field_simp
    try ring
  have hTsq : T ^ 2 = βL * μ₀ ^ 4 * R ^ 4 * N ^ 4 / (M ^ 3 * mn) := by
    have hstep : T ^ 2 = (Real.sqrt βL) ^ 2 * (μ₀ ^ 2) ^ 2
        * (Real.rpow ((N * R) / M) ((3 : ℝ) / 2)) ^ 2
        * (Real.sqrt ((N * R) / mn)) ^ 2 := by rw [hT]; ring
    rw [hstep, hsqrt_βL, hrpow_sq, hsqrt_NRmn]
    field_simp
    try ring
  have hQeqT : Q ^ 2 = T ^ 2 := by rw [hQsq', hTsq]
  nlinarith [hQeqT, hQnn, hTnn, sq_nonneg (T - Q)]

set_option maxHeartbeats 3200000 in
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
                (quadraticNeumannFirstIndexDistinctMeanContribution Omega S
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
                      ((3 : ℝ) / 2) +
                    Real.sqrt (β * logN) * μ₀ ^ 2 *
                        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
                          Real.sqrt ((N * R) / (↑(min n₁ n₂)))))) ≥
          1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases fixed_matrix_centered_sampling_spectral_bound with ⟨Cfixed, hCfixed, hFixed⟩
  rcases quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_min_dim with
    ⟨C68, hC68, hCoef⟩
  refine ⟨max 1 (Cfixed * C68), 1, ?_, one_pos, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set N : ℝ := ((max n₁ n₂ : ℕ) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mobs : ℝ := (m : ℝ) with hMobs
  set logN : ℝ := Real.log N with hlogN
  set Cout : ℝ := max 1 (Cfixed * C68) with hCout
  have hCfixed0 : 0 ≤ Cfixed := le_of_lt hCfixed
  have hC680 : 0 ≤ C68 := le_of_lt hC68
  have hCfC0 : 0 ≤ Cfixed * C68 := by positivity
  have hCfC_le : Cfixed * C68 ≤ Cout := le_max_right _ _
  have hCout_nonneg : 0 ≤ Cout := le_trans zero_le_one (le_max_left _ _)
  have hN_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < N := by rw [hN]; exact_mod_cast hN_nat
  have hN_one : 1 ≤ N := by rw [hN]; exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hR_pos : 0 < R := by rw [hR]; exact_mod_cast hr
  have hR_one : 1 ≤ R := by rw [hR]; exact_mod_cast (Nat.succ_le_of_lt hr)
  have hlogN_nonneg : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN_one
  have hβ_nonneg : 0 ≤ β := by linarith
  have hμ₀_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁_nonneg : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  obtain ⟨hp0, hp1⟩ : 0 ≤ p ∧ p ≤ 1 := by
    constructor
    · rw [hp]; positivity
    · rw [hp, div_le_one (by positivity)]
      have : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by exact_mod_cast hm
      exact this
  have hOne_le : (1 : ℝ) ≤ C' := le_trans (le_max_left _ _) hC'
  have hSampleFixed :
      (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) :=
    general_sample_bound_implies_fixed_matrix_sample_lower hOne_le hβ hn₁ hr hμ₁ hmLower
  -- Theorem 6.3 applied to H
  set Hmat : Matrix (Fin n₁) (Fin n₂) ℝ :=
    quadraticFirstIndexDistinctMeanCoefficientMatrix S p with hHmat
  have hFixedProb :
      bernoulliEventProb p
          (fun Omega =>
            CenteredSamplingSpectralBound Omega p Hmat
              (Cfixed * Real.sqrt
                ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
                entrySupNorm Hmat)) ≥
        1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
    simpa [hp] using
      hFixed β hβ n₁ n₂ m Hmat hn₁ hn₂ hm hSampleFixed
  refine le_trans hFixedProb ?_
  refine bernoulli_event_probability_mono (n₁ := n₁) (n₂ := n₂) p
    (fun Omega =>
      CenteredSamplingSpectralBound Omega p Hmat
        (Cfixed * Real.sqrt
          ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
          entrySupNorm Hmat))
    (fun Omega =>
      spectralNorm
        (quadraticNeumannFirstIndexDistinctMeanContribution Omega S p) ≤ _)
    hp0 hp1 ?_
  intro Omega hΩ
  rw [CenteredSamplingSpectralBound] at hΩ
  -- rewrite the mean contribution via the identity
  rw [quadratic_neumann_first_index_distinct_mean_as_coefficient_fluctuation Omega S p]
  by_cases hβL : 1 ≤ β * logN
  · have hβlog_pos : 0 < β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
      rw [← hN, ← hlogN]
      have : 0 < N * (β * logN) := by
        have := lt_of_lt_of_le one_pos hβL; positivity
      nlinarith [this, hN_pos, lt_of_lt_of_le one_pos hβL]
    have hm_pos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hmz | hmp
      · exfalso
        have hzero : ((m : ℝ)) = 0 := by rw [hmz]; norm_num
        rw [hzero] at hSampleFixed; linarith [hSampleFixed, hβlog_pos]
      · exact hmp
    have hMobs_pos : 0 < Mobs := by rw [hMobs]; exact_mod_cast hm_pos
    have hp_pos : 0 < p := by rw [hp]; positivity
    -- honest entry bound: C68·p⁻¹·(μ₀R/min)·(μ₁√(R/nn) + μ₀R/min)
    have hmn_pos : 0 < ((min n₁ n₂ : ℕ) : ℝ) := by
      have : 0 < min n₁ n₂ := lt_min hn₁ hn₂; exact_mod_cast this
    set mn : ℝ := ((min n₁ n₂ : ℕ) : ℝ) with hmn
    have hmnN : mn ≤ N := by
      rw [hmn, hN]; exact_mod_cast (min_le_max : min n₁ n₂ ≤ max n₁ n₂)
    have hnn_eq : (n₁ : ℝ) * (n₂ : ℝ) = N * mn := by
      rw [hN, hmn]; exact prod_eq_max_mul_min n₁ n₂
    set B : ℝ := μ₀ * R / mn with hB
    set sq : ℝ := μ₁ * Real.sqrt (R / ((n₁ : ℝ) * (n₂ : ℝ))) with hsq
    have hEntryH : entrySupNorm Hmat ≤ C68 * p⁻¹ * B * (sq + B) := by
      rw [hHmat]
      have := hCoef n₁ n₂ r M μ₀ μ₁ S p hn₁ hn₂ hr hp_pos hμ₀ hμ₁ hA0 hA1
      -- align B, sq with the node's RHS
      have halign :
          C68 * p⁻¹ *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
              (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                μ₀ * (r : ℝ) / (↑(min n₁ n₂)))
          = C68 * p⁻¹ * B * (sq + B) := by
        rw [hB, hsq, hR, hmn]
      rw [← halign]; exact this
    -- spectralNorm(fluct H) ≤ Cfixed·√(βNlogN/p)·entrySup H ≤ Cfixed·√·(honest coef)
    have hsqrteq :
        Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) =
          Real.sqrt (N * (β * logN) / p) := by
      rw [hN, hlogN]; congr 1; ring
    have hfac_nonneg :
        0 ≤ Cfixed * Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) := by
      positivity
    have hstep0 :
        spectralNorm (centeredSamplingFluctuation Omega p Hmat) ≤
          Cfixed * Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
            (C68 * p⁻¹ * B * (sq + B)) :=
      le_trans hΩ (mul_le_mul_of_nonneg_left hEntryH hfac_nonneg)
    -- the fluctuation rate = Cfixed·C68·√(NβL/p)·p⁻¹·B·(sq+B)
    have hSp_pos : 0 < Real.sqrt (N * (β * logN) / p) := by
      apply Real.sqrt_pos.mpr; positivity
    -- Split B·(sq+B) = B·sq + B²; bound each via Ba_le_term4 / Bb_le_term5
    set t4 : ℝ := Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) with ht4
    set t5 : ℝ :=
      Real.sqrt (β * logN) * μ₀ ^ 2 *
        Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) *
          Real.sqrt ((N * R) / mn) with ht5
    have hp_eq : p = Mobs / ((n₁ : ℝ) * (n₂ : ℝ)) := by rw [hp, hMobs]
    have hp_eq' : p = Mobs / (N * mn) := by rw [hp_eq, hnn_eq]
    have hBa :=
      Ba_le_term4 μ₀ μ₁ N R (β * logN) p (N * mn) mn Mobs rfl hp_eq'
        hN_pos hR_one hMobs_pos hmn_pos hmnN hβL hμ₀ hμ₁
    have hBb :=
      Bb_le_term5 μ₀ N R (β * logN) p (N * mn) mn Mobs rfl hp_eq'
        hN_pos hR_one hMobs_pos hmn_pos hβL hμ₀
    -- align the √(R/nn) in `sq` with √(R/(N mn))
    have hsq_eq : sq = μ₁ * Real.sqrt (R / (N * mn)) := by
      rw [hsq, hR, hnn_eq]
    -- rate = √(NβL/p)·p⁻¹·B·(sq+B) = [√(NβL/p)·p⁻¹·B·sq] + [√(NβL/p)·p⁻¹·B²]
    have hrate_split :
        Real.sqrt (N * (β * logN) / p) * p⁻¹ * B * (sq + B) =
          (Real.sqrt (N * (β * logN) / p) * p⁻¹ * (μ₀ * R / mn) *
              (μ₁ * Real.sqrt (R / (N * mn)))) +
          (Real.sqrt (N * (β * logN) / p) * p⁻¹ * (μ₀ * R / mn) ^ 2) := by
      rw [hB, hsq_eq]; ring
    have hrate_le :
        Real.sqrt (N * (β * logN) / p) * p⁻¹ * B * (sq + B) ≤ t4 + t5 := by
      rw [hrate_split]
      have hBa' := hBa
      have hBb' := hBb
      rw [ht4, ht5]
      -- Ba_le_term4/Bb_le_term5 produce exactly these two summands' bounds
      linarith [hBa', hBb']
    -- assemble: spectralNorm(fluct H) ≤ Cfixed·C68·(t4+t5)
    have hstep1 :
        spectralNorm (centeredSamplingFluctuation Omega p Hmat) ≤
          (Cfixed * C68) *
            (Real.sqrt (N * (β * logN) / p) * p⁻¹ * B * (sq + B)) := by
      refine le_trans hstep0 (le_of_eq ?_)
      rw [hsqrteq]; ring
    have hstep2 :
        spectralNorm (centeredSamplingFluctuation Omega p Hmat) ≤
          (Cfixed * C68) * (t4 + t5) :=
      le_trans hstep1 (mul_le_mul_of_nonneg_left hrate_le hCfC0)
    -- (1-p)·spectralNorm ≤ (Cfixed·C68)·(t4+t5)
    have h1p_nonneg : 0 ≤ 1 - p := by linarith [hp1]
    have hspec_smul :
        spectralNorm ((1 - p) • centeredSamplingFluctuation Omega p Hmat) =
          (1 - p) * spectralNorm (centeredSamplingFluctuation Omega p Hmat) := by
      rw [spectralNorm_smul, abs_of_nonneg h1p_nonneg]
    have ht4_nonneg : 0 ≤ t4 := by
      rw [ht4]; apply Real.rpow_nonneg; positivity
    have ht5_nonneg : 0 ≤ t5 := by
      rw [ht5]
      have := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (N * R) / Mobs) ((3:ℝ)/2)
      have h2 := Real.sqrt_nonneg ((N * R) / mn)
      positivity
    have hspec_le :
        spectralNorm ((1 - p) • centeredSamplingFluctuation Omega p Hmat) ≤
          (Cfixed * C68) * (t4 + t5) := by
      rw [hspec_smul]
      calc (1 - p) * spectralNorm (centeredSamplingFluctuation Omega p Hmat)
          ≤ 1 * ((Cfixed * C68) * (t4 + t5)) := by
            apply mul_le_mul _ hstep2 (spectralNorm_nonneg _) (by norm_num)
            linarith [hp0]
        _ = (Cfixed * C68) * (t4 + t5) := by ring
    -- (t4 + t5) ≤ Φ_corr and Cfixed·C68 ≤ Cout
    set term₁ : ℝ :=
      (μ₀ ^ 2 * μ₁) * Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2 with ht1
    set term₂ : ℝ := μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 with ht2
    set term₃ : ℝ :=
      Real.sqrt (β * logN) * Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) with ht3
    have h1n : 0 ≤ term₁ := by rw [ht1]; positivity
    have h2n : 0 ≤ term₂ := by rw [ht2]; positivity
    have h3n : 0 ≤ term₃ := by
      rw [ht3]
      have := Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (N * R) / Mobs) ((3:ℝ)/2)
      positivity
    have hΦ : t4 + t5 ≤ term₁ + term₂ + term₃ + t4 + t5 := by linarith
    have hfinal :
        spectralNorm ((1 - p) • centeredSamplingFluctuation Omega p Hmat) ≤
          Cout * (term₁ + term₂ + term₃ + t4 + t5) := by
      refine le_trans hspec_le ?_
      calc (Cfixed * C68) * (t4 + t5) ≤ Cout * (t4 + t5) :=
            mul_le_mul_of_nonneg_right hCfC_le (by linarith)
        _ ≤ Cout * (term₁ + term₂ + term₃ + t4 + t5) :=
            mul_le_mul_of_nonneg_left hΦ hCout_nonneg
    show spectralNorm _ ≤ _
    simpa [hCout, hN, hR, hMobs, hlogN, hmn, ht1, ht2, ht3, ht4, ht5] using hfinal
  · -- edge: β·logN < 1, β>2 ⟹ N = 1 ⟹ logN = 0 ⟹ RHS-scale ≥ 0, fluct-bound = 0
    have hβLsmall : β * logN < 1 := lt_of_not_ge hβL
    have hlogN_lt : logN < 1 / 2 := by
      by_contra hle
      push_neg at hle
      have : (1 : ℝ) ≤ β * logN := by nlinarith [hβ, hle, hlogN_nonneg]
      linarith [hβLsmall, this]
    have hN_lt2 : N < 2 := by
      by_contra hge
      push_neg at hge
      have : Real.log 2 ≤ logN := by rw [hlogN]; exact Real.log_le_log (by norm_num) hge
      have hlog2 : (0.6931 : ℝ) ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; norm_num at this ⊢; linarith [this]
      linarith [hlogN_lt, this, hlog2]
    have hN_eq1 : N = 1 := by
      have hNnat_le : max n₁ n₂ < 2 := by
        by_contra hh
        push_neg at hh
        have : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hh
        linarith [hN_lt2, this]
      have : max n₁ n₂ = 1 := by omega
      rw [hN, this]; norm_num
    have hlogN_zero : logN = 0 := by rw [hlogN, hN_eq1]; simp
    have hsqrt_zero :
        Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) = 0 := by
      have : (β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) = 0 := by
        rw [← hN, ← hlogN, hlogN_zero]; ring
      rw [this]; simp
    have hΩ0 :
        spectralNorm (centeredSamplingFluctuation Omega p Hmat) ≤ 0 := by
      have : Cfixed * Real.sqrt ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
              entrySupNorm Hmat = 0 := by rw [hsqrt_zero]; ring
      rw [this] at hΩ; exact hΩ
    have h1p_nonneg : 0 ≤ 1 - p := by linarith [hp1]
    have hspec_le0 :
        spectralNorm ((1 - p) • centeredSamplingFluctuation Omega p Hmat) ≤ 0 := by
      rw [spectralNorm_smul, abs_of_nonneg h1p_nonneg]
      have := mul_le_mul_of_nonneg_left hΩ0 h1p_nonneg
      simpa using this
    refine le_trans hspec_le0 ?_
    have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
    have hlog_cast_nonneg : 0 ≤ Real.log (↑(max n₁ n₂) : ℝ) := by
      rw [← hN, ← hlogN]; exact hlogN_nonneg
    simp only
    rw [hCout, hN, hR, hMobs]
    apply mul_nonneg hCout_nonneg
    have hbaseN_nonneg : 0 ≤ ((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ)) := by positivity
    have hbase4_nonneg :
        0 ≤ (μ₀ * μ₁ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂) : ℝ)) / (m : ℝ)) := by positivity
    have ht1 : 0 ≤
        μ₀ ^ 2 * μ₁ *
          Real.sqrt (((↑(max n₁ n₂) : ℝ) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂) : ℝ))) / (m : ℝ)) *
          (((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ)) ^ 2) := by positivity
    have ht2 : 0 ≤
        μ₀ ^ 2 * (((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ)) ^ 2) := by positivity
    have ht3 : 0 ≤
        Real.sqrt (β * Real.log (↑(max n₁ n₂) : ℝ)) *
          Real.rpow (((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ))) ((3 : ℝ) / 2) *
          (μ₀ ^ 2 * (r : ℝ)) := by
      have := Real.rpow_nonneg hbaseN_nonneg ((3 : ℝ) / 2); positivity
    have ht4 : 0 ≤
        Real.rpow
          ((μ₀ * μ₁ * (↑(max n₁ n₂) : ℝ) * (r : ℝ) *
            (β * Real.log (↑(max n₁ n₂) : ℝ))) / (m : ℝ))
          ((3 : ℝ) / 2) := Real.rpow_nonneg hbase4_nonneg _
    have ht5 : 0 ≤
        Real.sqrt (β * Real.log (↑(max n₁ n₂) : ℝ)) * μ₀ ^ 2 *
          Real.rpow (((↑(max n₁ n₂) : ℝ) * (r : ℝ) / (m : ℝ))) ((3 : ℝ) / 2) *
          Real.sqrt (((↑(max n₁ n₂) : ℝ) * (r : ℝ)) / (↑(min n₁ n₂))) := by
      have := Real.rpow_nonneg hbaseN_nonneg ((3 : ℝ) / 2)
      have h2 := Real.sqrt_nonneg (((↑(max n₁ n₂) : ℝ) * (r : ℝ)) / (↑(min n₁ n₂)))
      positivity
    nlinarith
