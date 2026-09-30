-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_coefficients_from_kernel_square_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:29:46.920679+00:00
-- url     : https://prove2.me/submissions/3e7459d3-802a-4cd3-b8e6-221c044f11b6

import Definitions.Def_matrix_completion_svd
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails

/- Complete component: SvdLeverage.lean; author /root/solver_resume, complete accepted Round42 reuse.
Source SHA256 d0afce6765032f7a3970d12f85ee70eb24ab340c4342e5b77b7cae363bae3546. Only import headers consolidated. -/
section Component1
namespace MatrixThreshold

open MatrixCompletion
open scoped BigOperators

theorem sum_sq_orthonormal_combination {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (c : I -> Real) (v : I -> J -> Real)
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) :
    ∑ j, (∑ k, c k * v k j) ^ 2 = ∑ k, c k ^ 2 := by
  classical
  calc
    _ = ∑ k, ∑ l, c k * c l * (∑ j, v k j * v l j) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp [hv, pow_two]

theorem orthonormal_leverage_le_one {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (v : I -> J -> Real)
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) (i : J) :
    ∑ k, (v k i) ^ 2 <= 1 := by
  classical
  have h := sum_sq_orthonormal_combination (fun k => v k i) v hv
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => sq_nonneg (∑ k, v k i * v k j))
    (Finset.mem_univ i)
  rw [h] at hle
  simp only [← pow_two] at hle
  nlinarith [sq_nonneg ((∑ k, (v k i) ^ 2) - 1)]

theorem sign_row_sq_sum_eq_leverage {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) :
    ∑ j, (signMatrix S i j) ^ 2 = ∑ k, (S.u k i) ^ 2 := by
  simpa [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply] using
    sum_sq_orthonormal_combination (fun k => S.u k i) S.v S.v_orthonormal

theorem sign_column_sq_sum_eq_leverage {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (j : Fin n2) :
    ∑ i, (signMatrix S i j) ^ 2 = ∑ k, (S.v k j) ^ 2 := by
  simpa [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm] using
    sum_sq_orthonormal_combination (fun k => S.v k j) S.u S.u_orthonormal

theorem row_leverage_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) : ∑ k, (S.u k i) ^ 2 <= 1 :=
  orthonormal_leverage_le_one S.u S.u_orthonormal i

theorem column_leverage_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (j : Fin n2) : ∑ k, (S.v k j) ^ 2 <= 1 :=
  orthonormal_leverage_le_one S.v S.v_orthonormal j

theorem sign_sq_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hmu : 0 <= mu) (hA1 : A1 S mu)
    (i : Fin n1) (j : Fin n2) :
    (signMatrix S i j) ^ 2 <= mu ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real)) := by
  have h := sq_le_sq₀ (abs_nonneg (signMatrix S i j))
    (mul_nonneg hmu (Real.sqrt_nonneg ((r : Real) / ((n1 : Real) * (n2 : Real)))))
  have hs := h.mpr (hA1 i j)
  rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)] at hs
  convert hs using 1
  ring

theorem row_leverage_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hmu : 0 <= mu) (hA1 : A1 S mu) (i : Fin n1) :
    ∑ k, (S.u k i) ^ 2 <= mu ^ 2 * (r : Real) / (n1 : Real) := by
  rw [← sign_row_sq_sum_eq_leverage S i]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    sign_sq_le_of_A1 S mu hmu hA1 i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  field_simp

theorem column_leverage_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hmu : 0 <= mu) (hA1 : A1 S mu) (j : Fin n2) :
    ∑ k, (S.v k j) ^ 2 <= mu ^ 2 * (r : Real) / (n2 : Real) := by
  rw [← sign_column_sq_sum_eq_leverage S j]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    sign_sq_le_of_A1 S mu hmu hA1 i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  field_simp

end MatrixThreshold

end Component1

/- Complete component: ScalarFourthThird.lean; author /root.
Source SHA256 2eb482c32277738e0978f638152691263cb1c69d8cafcb5e1d2b43ce0fdc67db. Only import headers consolidated. -/
section Component2
namespace QuadraticCoefficient

theorem normalized_power_bounds (x n lam K : Real)
    (hx : 1 <= x) (hn : 0 < n) (hlam : 1 <= lam)
    (hsize : lam * Real.rpow x ((4 : Real) / 3) <= n)
    (hdensity : lam * K * Real.rpow x ((4 : Real) / 3) <= n) :
    lam * K * (x / n) ^ 2 <= 1 ∧
      lam ^ 2 * K * (x / n) ^ 3 <= 1 := by
  have hx0 : 0 < x := by linarith
  have hlam0 : 0 <= lam := by linarith
  let A := Real.rpow x ((4 : Real) / 3)
  let B := Real.rpow x ((2 : Real) / 3)
  let C := Real.rpow x ((1 : Real) / 3)
  have hA0 : 0 <= A := Real.rpow_nonneg hx0.le _
  have hB0 : 0 <= B := Real.rpow_nonneg hx0.le _
  have hC0 : 0 <= C := Real.rpow_nonneg hx0.le _
  have hAn : A <= n := by
    calc
      A <= lam * A := by nlinarith [mul_nonneg (sub_nonneg.mpr hlam) hA0]
      _ <= n := hsize
  have hBA : B <= A := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hCA : C <= A := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hx2 : x ^ 2 = A * B := by
    dsimp [A, B]
    rw [← Real.rpow_add hx0]
    norm_num
  have hx3 : x ^ 3 = A * A * C := by
    dsimp [A, C]
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
    norm_num
  have hentry : lam * K * x ^ 2 <= n ^ 2 := by
    calc
      lam * K * x ^ 2 = (lam * K * A) * B := by rw [hx2]; ring
      _ <= n * B := mul_le_mul_of_nonneg_right hdensity hB0
      _ <= n * n := mul_le_mul_of_nonneg_left (hBA.trans hAn) hn.le
      _ = _ := by ring
  have hfrob : lam ^ 2 * K * x ^ 3 <= n ^ 3 := by
    have hp : (lam * K * A) * (lam * A) <= n * n :=
      mul_le_mul hdensity hsize (mul_nonneg hlam0 hA0) hn.le
    calc
      lam ^ 2 * K * x ^ 3 = ((lam * K * A) * (lam * A)) * C := by rw [hx3]; ring
      _ <= (n * n) * C := mul_le_mul_of_nonneg_right hp hC0
      _ <= (n * n) * n := mul_le_mul_of_nonneg_left (hCA.trans hAn) (by positivity)
      _ = _ := by ring
  constructor
  · rw [div_pow, ← mul_div_assoc]
    exact (div_le_one (by positivity : 0 < n ^ 2)).mpr hentry
  · rw [div_pow, ← mul_div_assoc]
    exact (div_le_one (by positivity : 0 < n ^ 3)).mpr hfrob

theorem raw_scale_absorption (x n lam K q Ce Cf : Real)
    (hx : 1 <= x) (hn : 0 < n) (hlam : 1 <= lam) (hK : 0 <= K)
    (hq : q <= 2) (hCe : 0 <= Ce) (hCf : 0 <= Cf)
    (hsize : lam * Real.rpow x ((4 : Real) / 3) <= n)
    (hdensity : lam * K * Real.rpow x ((4 : Real) / 3) <= n) :
    Real.sqrt (q * K) * Cf * Real.rpow (x / n) ((3 : Real) / 2) +
      (q * K) * Ce * (x / n) ^ 2 <= 2 * (Cf + Ce) / lam := by
  have hlam0 : 0 < lam := by linarith
  have hxn : 0 <= x / n := by positivity
  have hpow0 : 0 <= Real.rpow (x / n) ((3 : Real) / 2) := Real.rpow_nonneg hxn _
  obtain ⟨hentry, hfrob⟩ := normalized_power_bounds x n lam K hx hn hlam hsize hdensity
  have hqK : q * K <= 2 * K := mul_le_mul_of_nonneg_right hq hK
  have hpow : (Real.rpow (x / n) ((3 : Real) / 2)) ^ 2 = (x / n) ^ 3 := by
    convert (Real.rpow_mul hxn ((3 : Real) / 2) 2).symm using 1 <;> norm_num
  have hsq : (lam * (Real.sqrt (2 * K) * Real.rpow (x / n) ((3 : Real) / 2))) ^ 2 <= 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), hpow]
    nlinarith
  have hroot : lam * (Real.sqrt (2 * K) * Real.rpow (x / n) ((3 : Real) / 2)) <= 2 := by
    nlinarith [sq_nonneg (lam * (Real.sqrt (2 * K) * Real.rpow (x / n) ((3 : Real) / 2)) - 1)]
  have hsqrt : Real.sqrt (q * K) * Real.rpow (x / n) ((3 : Real) / 2) <= 2 / lam := by
    apply (le_div_iff₀ hlam0).mpr
    calc
      _ <= (Real.sqrt (2 * K) * Real.rpow (x / n) ((3 : Real) / 2)) * lam :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hqK) hpow0) hlam0.le
      _ <= 2 := by simpa only [mul_comm] using hroot
  have hlinear : (q * K) * (x / n) ^ 2 <= 2 / lam := by
    apply (le_div_iff₀ hlam0).mpr
    calc
      _ <= ((2 * K) * (x / n) ^ 2) * lam :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqK (sq_nonneg _)) hlam0.le
      _ <= 2 := by nlinarith
  calc
    _ = Cf * (Real.sqrt (q * K) * Real.rpow (x / n) ((3 : Real) / 2)) +
        Ce * ((q * K) * (x / n) ^ 2) := by ring
    _ <= Cf * (2 / lam) + Ce * (2 / lam) := add_le_add
      (mul_le_mul_of_nonneg_left hsqrt hCf) (mul_le_mul_of_nonneg_left hlinear hCe)
    _ = _ := by ring

end QuadraticCoefficient

end Component2

/- Complete component: CoefficientTools.lean; author /root/truncation_resume.
Source SHA256 08fd82863ba59c809d7ea3ceb743ceccec348fb5e7ac96d38a5612b1d1232844. Only import headers consolidated. -/
section Component3
namespace QuadraticCoefficient

open MatrixCompletion
open scoped BigOperators

theorem sign_abs_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) (j : Fin n2) : |signMatrix S i j| <= 1 := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ Finset.univ) => sq_nonneg (signMatrix S i k))
    (Finset.mem_univ j)
  rw [MatrixThreshold.sign_row_sq_sum_eq_leverage S i] at h
  have hle := h.trans (MatrixThreshold.row_leverage_le_one S i)
  nlinarith [sq_abs (signMatrix S i j), abs_nonneg (signMatrix S i j)]

theorem event_prob_nonneg {n1 n2 : Nat} (p : Real) (hp0 : 0 <= p) (hp1 : p <= 1)
    (E : Finset (Fin n1 × Fin n2) -> Prop) : 0 <= bernoulliEventProb p E := by
  classical
  unfold bernoulliEventProb
  apply Finset.sum_nonneg
  intro s hs
  have hw : 0 <= bernoulliObservationWeight p s := by
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  split_ifs <;> positivity

theorem event_prob_mono {n1 n2 : Nat} (p : Real) (hp0 : 0 <= p) (hp1 : p <= 1)
    (E F : Finset (Fin n1 × Fin n2) -> Prop) (hEF : ∀ s, E s -> F s) :
    bernoulliEventProb p E <= bernoulliEventProb p F := by
  classical
  unfold bernoulliEventProb
  apply Finset.sum_le_sum
  intro s hs
  have hw : 0 <= bernoulliObservationWeight p s := by
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)
  by_cases hE : E s
  · simp [hE, hEF s hE]
  · simp only [if_neg hE]
    split_ifs <;> positivity

theorem entry_sup_le {n1 n2 : Nat} (X : RealMatrix n1 n2) (a : Real)
    (ha : 0 <= a) (h : ∀ w : Fin n1 × Fin n2, |X w.1 w.2| <= a) :
    entrySupNorm X <= a :=
  Real.iSup_le (fun i => Real.iSup_le (fun j => h (i, j)) ha) ha

end QuadraticCoefficient

end Component3

/- Complete component: SamplingThreshold.lean; author /root/truncation_resume.
Source SHA256 dd683f2a0682cc81f4a8154917f42c3d9e84d207d1b7a159cf8172fbb7b4966f. Only import headers consolidated. -/
section Component4
namespace QuadraticCoefficient

theorem sampling_threshold_le (beta lam n N x m Ce Cf : Real)
    (hbeta : 2 < beta) (hlam : 1 <= lam) (hn2 : 2 <= n)
    (hN : 0 < N) (hNN : N <= n ^ 2) (hx : 1 <= x) (hmN : m <= N)
    (hCe : 0 <= Ce) (hCf : 0 <= Cf)
    (hfloor : lam * Real.rpow x ((4 : Real) / 3) * n * (beta * Real.log n) <= m) :
    Real.sqrt (((beta + 2) * Real.log n) / (m / N)) *
        (Cf * Real.rpow (x / n) ((3 : Real) / 2)) +
      (((beta + 2) * Real.log n) / (m / N)) * (Ce * (x / n) ^ 2) <=
        2 * (Cf + Ce) / lam := by
  have hn : 0 < n := by linarith
  have hx0 : 0 < x := by linarith
  have hlam0 : 0 < lam := by linarith
  have hbeta0 : 0 < beta := by linarith
  have hinv : n⁻¹ <= (1 : Real) / 2 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hn2
  have hlog : (1 : Real) / 2 <= Real.log n := by
    linarith [Real.one_sub_inv_le_log_of_pos hn]
  have hL : 1 <= beta * Real.log n := by nlinarith
  have hL0 : 0 < beta * Real.log n := lt_of_lt_of_le zero_lt_one hL
  have hm : 0 < m := lt_of_lt_of_le
    (mul_pos (mul_pos (mul_pos hlam0 (Real.rpow_pos_of_pos hx0 _)) hn) hL0) hfloor
  let A := Real.rpow x ((4 : Real) / 3)
  let K := beta * Real.log n * N / m
  let q := (beta + 2) / beta
  have hA : 0 < A := Real.rpow_pos_of_pos hx0 _
  have hK : 0 <= K := by dsimp [K]; positivity
  have hq : q <= 2 := by
    dsimp [q]
    exact (div_le_iff₀ hbeta0).mpr (by linarith)
  have hsize : lam * A <= n := by
    apply (mul_le_mul_iff_right₀ hn).mp
    calc
      n * (lam * A) = lam * A * n := by ring
      _ <= lam * A * n * (beta * Real.log n) :=
        le_mul_of_one_le_right (by positivity) hL
      _ <= m := hfloor
      _ <= N := hmN
      _ <= n * n := by nlinarith [hNN]
  have hdensity : lam * K * A <= n := by
    apply (mul_le_mul_iff_right₀ hn).mp
    calc
      n * (lam * K * A) = (lam * A * n * (beta * Real.log n)) * (N / m) := by
        dsimp [K]; ring
      _ <= m * (N / m) := mul_le_mul_of_nonneg_right hfloor (by positivity)
      _ = N := by field_simp
      _ <= n * n := by nlinarith [hNN]
  have hscale : ((beta + 2) * Real.log n) / (m / N) = q * K := by
    dsimp [q, K]
    field_simp
  rw [hscale]
  convert raw_scale_absorption x n lam K q Ce Cf hx hn hlam hK hq hCe hCf hsize hdensity using 1
  ring

end QuadraticCoefficient

end Component4

/- Complete component: Conclusion.lean; author /root/truncation_resume.
Source SHA256 86914d0972bd102a8b3cc29a525c38d6e1e172fb613178a137f00c73c6f5f1dc. Only import headers consolidated. -/
section Component5
open MatrixCompletion

theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ (Omega2 : Finset (Fin n₁ × Fin n₂))
            (w1 : Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1.1 w1.2 =
            signMatrix S w1.1 w1.2 *
              matrixEntrySum
                (centeredSamplingFluctuation Omega2
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                  (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Centry * μ₀ ^ 2 *
              (((r : ℝ) / (↑(max n₁ n₂))) ^ 2)) →
        (∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * Real.rpow lam (-1))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCe hCf
  obtain ⟨Cb, cb, hCb, hcb, hBern⟩ :=
    scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
  let Cp := 2 * Cb * (Cfro + Centry)
  have hCp : 0 < Cp := by dsimp [Cp]; positivity
  obtain ⟨Cu, cu, hCu, hcu, hUniform⟩ :=
    bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails Cp cb hCp hcb
  refine ⟨Cu, max 1 cu, hCu, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro beta lam hbeta hlam n1 n2 r m M mu0 mu1 S hn1 hn2 hr hm hmu0 hmu1 hA0 hA1 hsample
    hRep hEntry hFrob
  let n : Real := (max n1 n2 : Nat)
  let N : Real := (n1 : Real) * (n2 : Real)
  let x : Real := mu0 * (r : Real)
  let p : Real := (m : Real) / N
  have hN : 0 < N := by dsimp [N]; positivity
  have hmN : (m : Real) <= N := by dsimp [N]; exact_mod_cast hm
  have hp0 : 0 <= p := by dsimp [p]; positivity
  have hp1 : p <= 1 := (div_le_one hN).mpr hmN
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast lt_of_lt_of_le hn1 (le_max_left n1 n2)
  have hx : 1 <= x := one_le_mul_of_one_le_of_one_le hmu0 (by exact_mod_cast hr)
  by_cases hnLarge : 2 <= max n1 n2
  · have hnTwo : (2 : Real) <= n := by dsimp [n]; exact_mod_cast hnLarge
    have hNN : N <= n ^ 2 := by
      have h1 : (n1 : Real) <= n := by dsimp [n]; exact_mod_cast le_max_left n1 n2
      have h2 : (n2 : Real) <= n := by dsimp [n]; exact_mod_cast le_max_right n1 n2
      have h := mul_le_mul h1 h2 (by positivity : (0 : Real) <= n2) hn.le
      dsimp [N]
      nlinarith
    have hfloor : lam * Real.rpow x ((4 : Real) / 3) * n * (beta * Real.log n) <= (m : Real) := by
      dsimp [x, n]
      rw [Real.mul_rpow (by linarith : 0 <= mu0) (by positivity : (0 : Real) <= r)]
      simpa only [Real.rpow_eq_pow, mul_assoc, mul_left_comm, mul_comm] using hsample
    have hthreshold := QuadraticCoefficient.sampling_threshold_le beta lam n N x m Centry Cfro
      hbeta hlam hnTwo hN hNN hx hmN hCe.le hCf.le hfloor
    have hpow : Real.rpow (x / n) ((3 : Real) / 2) =
        Real.rpow mu0 ((3 : Real) / 2) * Real.rpow ((r : Real) / n) ((3 : Real) / 2) := by
      dsimp [x]
      rw [mul_div_assoc, Real.mul_rpow (by linarith : 0 <= mu0) (by positivity)]
    have hbound : Cb * (Real.sqrt (((beta + 2) * Real.log n) / p) *
        (Cfro * Real.rpow (x / n) ((3 : Real) / 2)) +
        (((beta + 2) * Real.log n) / p) * (Centry * (x / n) ^ 2)) <=
        Cp * Real.rpow lam (-1) := by
      calc
        _ <= Cb * (2 * (Cfro + Centry) / lam) := mul_le_mul_of_nonneg_left hthreshold hCb.le
        _ = _ := by rw [Real.rpow_eq_pow, Real.rpow_neg_one]; dsimp [Cp]; ring
    have hPoint : ∀ w : Fin n1 × Fin n2,
        bernoulliEventProb p (fun Omega =>
          |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega S p w.1 w.2| <=
            Cp * Real.rpow lam (-1)) >= 1 - cb * Real.rpow n (-(beta + 2)) := by
      intro w
      have hEn : entrySupNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w) <=
          Centry * (x / n) ^ 2 := by
        convert hEntry w using 1
        dsimp [x, n]
        ring
      have hFn : frobeniusNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w) <=
          Cfro * Real.rpow (x / n) ((3 : Real) / 2) := by
        rw [hpow]
        simpa only [mul_assoc] using hFrob w
      have hRaw := hBern (beta + 2) (by linarith) n1 n2 m hn1 hn2 hm
        (fun Omega => matrixEntrySum (centeredSamplingFluctuation Omega p
          (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w)))
        (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w)
        (Centry * (x / n) ^ 2) (Cfro * Real.rpow (x / n) ((3 : Real) / 2))
        (fun Omega => rfl) hEn hFn
      apply le_trans hRaw
      apply QuadraticCoefficient.event_prob_mono p hp0 hp1
      intro Omega hOmega
      calc
        _ = |signMatrix S w.1 w.2| * |matrixEntrySum (centeredSamplingFluctuation Omega p
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w))| := by rw [hRep, abs_mul]
        _ <= |matrixEntrySum (centeredSamplingFluctuation Omega p
            (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w))| :=
          mul_le_of_le_one_left (abs_nonneg _) (QuadraticCoefficient.sign_abs_le_one S w.1 w.2)
        _ <= _ := hOmega.trans hbound
    have hAll := hUniform beta p (Real.rpow lam (-1)) hbeta hp0 hp1 n1 n2 hn1 hn2
      (fun w Omega => quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega S p w.1 w.2) hPoint
    have hfail : 1 - max 1 cu * Real.rpow n (-beta) <= 1 - cu * Real.rpow n (-beta) := by
      have h := mul_le_mul_of_nonneg_right (le_max_right (1 : Real) cu)
        (Real.rpow_nonneg hn.le (-beta))
      simpa only [Real.rpow_eq_pow] using sub_le_sub_left h 1
    apply le_trans hfail
    apply le_trans hAll
    apply QuadraticCoefficient.event_prob_mono p hp0 hp1
    intro Omega hOmega
    exact QuadraticCoefficient.entry_sup_le _ (Cu * Real.rpow lam (-1))
      (mul_nonneg hCu.le (Real.rpow_nonneg (by linarith) _)) hOmega
  · have hnOne : max n1 n2 = 1 := by omega
    have hfail : 1 - max 1 cu * Real.rpow n (-beta) <= 0 := by
      simp only [n, hnOne, Nat.cast_one, Real.rpow_eq_pow, Real.one_rpow, mul_one]
      linarith [le_max_left (1 : Real) cu]
    exact hfail.trans (QuadraticCoefficient.event_prob_nonneg p hp0 hp1 _)

end Component5

