-- Prove2me | solution 2 for quadratic_neumann_first_index_distinct_centered_decoupled_lemma67_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T09:23:31.087877+00:00
-- url     : https://prove2.me/submissions/2810a29c-e474-4cc0-9492-fc32c9728a71

import Theorems.Thm_centered_sampling_spectral_event_from_a0_energy_moment
import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
import Theorems.Thm_quadratic_neumann_first_index_distinct_centered_decoupled_as_coefficient_fluctuation
import Theorems.Thm_bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

set_option maxHeartbeats 1000000

/-!
# §6.3 first-index centered decoupled Lemma-6.7 brick (brick 1)

The genuine §6.3 analytic content of the centered `ω₁ ≠ ω₂ = ω₃` case, as a
two-copy decoupled pair estimate at the four-term summary scale `Φ`.

Composition (all ingredients Proved/banked):

* the tight coefficient entrySup EVENT over the inner copy `Ω₂`
  (`quadratic_neumann_first_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim`)
  bounds `‖coefMatrix Ω₂‖∞ ≤ Ccoef · twoTerm`;
* node (iv)
  (`centered_sampling_spectral_event_from_a0_energy_moment`) applied to
  `X = coefMatrix Ω₂` produces the outer spectral EVENT over `Ω₁`:
  `spectralNorm (centeredSamplingFluctuation Ω₁ p coefMatrix) ≤ Ctail·√q·p⁻¹·√EnergyBound`;
* the rep identity
  (`quadratic_neumann_first_index_distinct_centered_decoupled_as_coefficient_fluctuation`)
  rewrites the decoupled contribution as `(p⁻¹(1-2p)) • centeredSamplingFluctuation Ω₁ p coefMatrix`;
* the two scales combine to the third summary term `Φ₃` of `Φ`
  (numerically gated, `≤ 0.06·Φ`), using the `μ₁²`-part of the general sample
  lower bound to absorb the extra oversampling factor;
* the outer conditional and inner marginal events are combined by the generic
  product-Bernoulli pair lift.

Source: Candès–Recht 2008, §6.3, PDF pp. 31--32, Lemma 6.7 and the p. 34 summary.
-/

namespace MatrixCompletion

/-- Total Bernoulli observation weight is 1. -/
private lemma bernoulliObservationWeight_sum_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ, Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard : (Finset.univ : Finset α).card = N := by simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α, p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl; intro k hk; ring
    _ = (p + (1 - p)) ^ N := by rw [add_pow]
    _ = 1 := by ring

/-- Scaling helper, copied from the closed all-equal / linear-diagonal centered
cases: `spectralNorm (a • X) ≤ |a| · spectralNorm X`. -/
private lemma spectralNorm_smul_le_abs
    {n₁ n₂ : ℕ} (a : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (a • X) ≤ |a| * spectralNorm X := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (a • X)) =
        a • LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin, norm_smul]
  simp [Real.norm_eq_abs]

/-- `n₁·n₂ / min = max`. -/
private lemma max_mul_min_cast_div
    {n₁ n₂ : ℕ} (hmin : 0 < min n₁ n₂) :
    ((n₁ : ℝ) * (n₂ : ℝ)) / ((min n₁ n₂ : ℕ) : ℝ) =
      ((max n₁ n₂ : ℕ) : ℝ) := by
  have hprod_nat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ := max_mul_min n₁ n₂
  have hprod :
      ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) =
        (n₁ : ℝ) * (n₂ : ℝ) := by exact_mod_cast hprod_nat
  have hmin_ne : ((min n₁ n₂ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hmin)
  calc
    ((n₁ : ℝ) * (n₂ : ℝ)) / ((min n₁ n₂ : ℕ) : ℝ)
        = (((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ)) /
            ((min n₁ n₂ : ℕ) : ℝ) := by rw [hprod]
    _ = ((max n₁ n₂ : ℕ) : ℝ) := by field_simp [hmin_ne]

/-- `|p⁻¹(1-2p)| ≤ n₁n₂/m` for `p = m/(n₁n₂)`, `0 < m ≤ n₁n₂`. -/
private lemma abs_two_prefactor_le_card_div_sample
    {n₁ n₂ m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hm : m ≤ n₁ * n₂)
    (hm_pos : 0 < m) :
    abs ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ *
        (1 - 2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))))) ≤
      ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := by
  have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
  have hm_pos_real : 0 < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hp_le_one : p ≤ 1 := by
    rw [hp, div_le_one hden_pos]; exact_mod_cast hm
  have hp_inv_eq : p⁻¹ = ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := by
    rw [hp]; field_simp
  have habs2 : |1 - 2 * p| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [hp_pos, hp_le_one]
  calc
    abs (p⁻¹ * (1 - 2 * p)) = |p⁻¹| * |1 - 2 * p| := by rw [abs_mul]
    _ = p⁻¹ * |1 - 2 * p| := by rw [abs_of_pos (by positivity)]
    _ ≤ p⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left habs2 (le_of_lt (by positivity))
    _ = p⁻¹ := by ring
    _ = ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := hp_inv_eq

/-- `y ^ (3/2) = y * √y` for `y ≥ 0`. -/
private lemma rpow_three_halves {y : ℝ} (hy : 0 ≤ y) :
    Real.rpow y ((3 : ℝ) / 2) = y * Real.sqrt y := by
  rcases eq_or_lt_of_le hy with h | h
  · rw [← h]; simp [Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0)]
  · have hrw : y * Real.sqrt y = y ^ (1 : ℝ) * y ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_one]
    rw [hrw, ← Real.rpow_add h]; norm_num

/-- Piece A of the Φ₃ mapping (Frobenius scale). -/
private lemma pieceA_le
    (N R M mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef : ℝ)
    (hN1 : 1 ≤ N) (hR1 : 1 ≤ R) (hmn_pos : 0 < mn)
    (hlog : 0 ≤ logN) (hβ : 2 < β)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hM_pos : 0 < M)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hCtail : 0 < Ctail) (hCenergy : 0 < Cenergy) (hCcoef : 0 < Ccoef)
    (hmlow : M ≥ μ₁ ^ 2 * N * R * (β * logN)) :
    ((nn / M) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        (Real.sqrt (((β + 2) * logN) / p) *
          (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn) * (μ₀ * R / mn))))
      ≤ (Ctail * Real.sqrt Cenergy * Ccoef * 2) *
        (Real.sqrt (β * logN) * Real.rpow (N * R / M) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)) := by
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hbl : 0 ≤ β * logN := by positivity
  have hb2l : 0 ≤ ((β + 2) * logN) / p := by positivity
  set L := ((nn / M) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        (Real.sqrt (((β + 2) * logN) / p) *
          (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn) * (μ₀ * R / mn)))) with hL
  set Rt := ((Ctail * Real.sqrt Cenergy * Ccoef * 2) *
        (Real.sqrt (β * logN) * Real.rpow (N * R / M) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R))) with hRt
  have hL_nonneg : 0 ≤ L := by
    rw [hL]; have : 0 ≤ nn / M := by positivity
    positivity
  have hRt_nonneg : 0 ≤ Rt := by
    rw [hRt]
    have : 0 ≤ Real.rpow (N * R / M) ((3 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    positivity
  have hL2 : L ^ 2 = 2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 4 * R ^ 4 * β * logN ^ 2 * μ₀ ^ 3 * μ₁ ^ 2 * (β + 2) / M ^ 4 := by
    rw [hL]
    have e1 : Real.sqrt (2 * (β * logN)) ^ 2 = 2 * (β * logN) := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (Cenergy * p * N) ^ 2 = Cenergy * p * N := Real.sq_sqrt (by positivity)
    have e3 : Real.sqrt (((β + 2) * logN) / p) ^ 2 = ((β + 2) * logN) / p := Real.sq_sqrt hb2l
    have e4 : Real.sqrt (R / nn) ^ 2 = R / nn := Real.sq_sqrt (by positivity)
    have e5 : Real.sqrt (μ₀ * R / mn) ^ 2 = μ₀ * R / mn := Real.sq_sqrt (by positivity)
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
        e1, e2, e3, e4, e5, hp, hnn]
    field_simp
  have hRt2 : Rt ^ 2 = 4 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 5 * β * logN * μ₀ ^ 4 / M ^ 3 := by
    rw [hRt]
    have e1 : Real.sqrt (β * logN) ^ 2 = β * logN := Real.sq_sqrt hbl
    have hrp : Real.rpow (N * R / M) ((3 : ℝ) / 2) = (N * R / M) * Real.sqrt (N * R / M) :=
      rpow_three_halves (by positivity)
    have e6 : Real.sqrt (N * R / M) ^ 2 = N * R / M := Real.sq_sqrt (by positivity)
    have e7 : Real.sqrt Cenergy ^ 2 = Cenergy := Real.sq_sqrt (le_of_lt hCenergy)
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, hrp, mul_pow, mul_pow, e1, e6, e7]
    field_simp; ring
  have hkey : N * logN * μ₁ ^ 2 * (β + 2) ≤ 2 * M * R * μ₀ := by
    have hRμ : (0 : ℝ) ≤ 2 * R * μ₀ := by positivity
    have hstep := mul_le_mul_of_nonneg_right hmlow hRμ
    have hR2μ : (1 : ℝ) ≤ R ^ 2 * μ₀ := by nlinarith [hR1, hμ₀, mul_pos hR0 hR0]
    have hfac : β + 2 ≤ 2 * R ^ 2 * μ₀ * β := by nlinarith [hR2μ, hβ]
    have hbase : (0 : ℝ) ≤ N * logN * μ₁ ^ 2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hfac hbase
    nlinarith [hstep, h2]
  have hL2_le : L ^ 2 ≤ Rt ^ 2 := by
    rw [hL2, hRt2, div_le_div_iff₀ (by positivity) (by positivity)]
    set mult : ℝ := 2 * (Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 4 * β * logN * μ₀ ^ 3 * M ^ 3) with hmult_def
    have hmult : (0 : ℝ) ≤ mult := by rw [hmult_def]; positivity
    have hscaled := mul_le_mul_of_nonneg_left hkey hmult
    have hLeq : 2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 4 * R ^ 4 * β * logN ^ 2 * μ₀ ^ 3 * μ₁ ^ 2 * (β + 2) * M ^ 3
        = mult * (N * logN * μ₁ ^ 2 * (β + 2)) := by rw [hmult_def]; ring
    have hReq : 4 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 5 * β * logN * μ₀ ^ 4 * M ^ 4
        = mult * (2 * M * R * μ₀) := by rw [hmult_def]; ring
    rw [hLeq, hReq]; exact hscaled
  nlinarith [sq_nonneg (Rt - L), sq_nonneg (Rt + L), hL2_le, hL_nonneg, hRt_nonneg]

/-- Piece B of the Φ₃ mapping (entry scale). -/
private lemma pieceB_le
    (N R M mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef : ℝ)
    (hN1 : 1 ≤ N) (hR1 : 1 ≤ R) (hmn_pos : 0 < mn)
    (hlog : 0 ≤ logN) (hβ : 2 < β)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hM_pos : 0 < M)
    (hnn : nn = N * mn) (hp : p = M / nn)
    (hCtail : 0 < Ctail) (hCenergy : 0 < Cenergy) (hCcoef : 0 < Ccoef)
    (hmlow : M ≥ μ₁ ^ 2 * N * R * (β * logN)) :
    ((nn / M) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        ((((β + 2) * logN) / p) *
          (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn) * (μ₀ * R / mn))))
      ≤ (Ctail * Real.sqrt Cenergy * Ccoef * 3) *
        (Real.sqrt (β * logN) * Real.rpow (N * R / M) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)) := by
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hbl : 0 ≤ β * logN := by positivity
  set L := ((nn / M) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ *
        Real.sqrt (Cenergy * p * N) * Ccoef *
        ((((β + 2) * logN) / p) *
          (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn) * (μ₀ * R / mn)))) with hL
  set Rt := ((Ctail * Real.sqrt Cenergy * Ccoef * 3) *
        (Real.sqrt (β * logN) * Real.rpow (N * R / M) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R))) with hRt
  have hL_nonneg : 0 ≤ L := by
    rw [hL]; have : 0 ≤ nn / M := by positivity
    have hb2 : 0 ≤ ((β + 2) * logN) / p := by positivity
    positivity
  have hRt_nonneg : 0 ≤ Rt := by
    rw [hRt]
    have : 0 ≤ Real.rpow (N * R / M) ((3 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    positivity
  have hL2 : L ^ 2 = 2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 5 * R ^ 5 * β * logN ^ 3 * μ₀ ^ 4 * μ₁ ^ 2 * (β + 2) ^ 2 / M ^ 5 := by
    rw [hL]
    have e1 : Real.sqrt (2 * (β * logN)) ^ 2 = 2 * (β * logN) := Real.sq_sqrt (by positivity)
    have e2 : Real.sqrt (Cenergy * p * N) ^ 2 = Cenergy * p * N := Real.sq_sqrt (by positivity)
    have e4 : Real.sqrt (R / nn) ^ 2 = R / nn := Real.sq_sqrt (by positivity)
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
        e1, e2, e4, hp, hnn]
    field_simp
  have hRt2 : Rt ^ 2 = 9 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 5 * β * logN * μ₀ ^ 4 / M ^ 3 := by
    rw [hRt]
    have e1 : Real.sqrt (β * logN) ^ 2 = β * logN := Real.sq_sqrt hbl
    have hrp : Real.rpow (N * R / M) ((3 : ℝ) / 2) = (N * R / M) * Real.sqrt (N * R / M) :=
      rpow_three_halves (by positivity)
    have e6 : Real.sqrt (N * R / M) ^ 2 = N * R / M := Real.sq_sqrt (by positivity)
    have e7 : Real.sqrt Cenergy ^ 2 = Cenergy := Real.sq_sqrt (le_of_lt hCenergy)
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, hrp, mul_pow, mul_pow, e1, e6, e7]
    field_simp; ring
  have hkey : 2 * N ^ 2 * logN ^ 2 * μ₁ ^ 2 * (β + 2) ^ 2 ≤ 9 * M ^ 2 := by
    have hMsq : μ₁ ^ 4 * N ^ 2 * R ^ 2 * β ^ 2 * logN ^ 2 ≤ M ^ 2 := by
      nlinarith [mul_le_mul hmlow hmlow (by positivity) (by positivity)]
    have hbeta : 2 * (β + 2) ^ 2 ≤ 9 * β ^ 2 := by nlinarith [hβ, sq_nonneg (β - 2)]
    have hR2 : (1 : ℝ) ≤ R ^ 2 := by nlinarith [hR1]
    have hμ12 : (1 : ℝ) ≤ μ₁ ^ 2 := by nlinarith [hμ₁]
    have hμ14 : μ₁ ^ 2 ≤ μ₁ ^ 4 := by nlinarith [mul_nonneg (sq_nonneg μ₁) (sub_nonneg.mpr hμ12)]
    calc 2 * N ^ 2 * logN ^ 2 * μ₁ ^ 2 * (β + 2) ^ 2
        = (N ^ 2 * logN ^ 2 * μ₁ ^ 2) * (2 * (β + 2) ^ 2) := by ring
      _ ≤ (N ^ 2 * logN ^ 2 * μ₁ ^ 2) * (9 * β ^ 2) :=
          mul_le_mul_of_nonneg_left hbeta (by positivity)
      _ ≤ (N ^ 2 * logN ^ 2 * μ₁ ^ 2) * (9 * (R ^ 2 * β ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_right hR2 (by positivity : (0 : ℝ) ≤ 9 * β ^ 2)]
      _ = 9 * (μ₁ ^ 2 * (N ^ 2 * R ^ 2 * β ^ 2 * logN ^ 2)) := by ring
      _ ≤ 9 * (μ₁ ^ 4 * (N ^ 2 * R ^ 2 * β ^ 2 * logN ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hμ14 (by positivity)
      _ = 9 * (μ₁ ^ 4 * N ^ 2 * R ^ 2 * β ^ 2 * logN ^ 2) := by ring
      _ ≤ 9 * M ^ 2 := by nlinarith [hMsq]
  have hL2_le : L ^ 2 ≤ Rt ^ 2 := by
    rw [hL2, hRt2, div_le_div_iff₀ (by positivity) (by positivity)]
    set mult : ℝ := Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 5 * β * logN * μ₀ ^ 4 * M ^ 3 with hmult_def
    have hmult : (0 : ℝ) ≤ mult := by rw [hmult_def]; positivity
    have hscaled := mul_le_mul_of_nonneg_left hkey hmult
    have hLeq : 2 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 5 * R ^ 5 * β * logN ^ 3 * μ₀ ^ 4 * μ₁ ^ 2 * (β + 2) ^ 2 * M ^ 3
        = mult * (2 * N ^ 2 * logN ^ 2 * μ₁ ^ 2 * (β + 2) ^ 2) := by rw [hmult_def]; ring
    have hReq : 9 * Ccoef ^ 2 * Cenergy * Ctail ^ 2 * N ^ 3 * R ^ 5 * β * logN * μ₀ ^ 4 * M ^ 5
        = mult * (9 * M ^ 2) := by rw [hmult_def]; ring
    rw [hLeq, hReq]; exact hscaled
  nlinarith [sq_nonneg (Rt - L), sq_nonneg (Rt + L), hL2_le, hL_nonneg, hRt_nonneg]

/-- Conditional pointwise bound: on the outer node-(iv) event (for the fixed
inner coefficient matrix) and the inner coefficient bound, the decoupled
contribution has spectral norm `≤ Ctail·√Cenergy·Ccoef·5 · Φ₃ ≤ (that)·Φ`. -/
private lemma conditional_pointwise_bound
    {n₁ n₂ r m : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (β μ₀ μ₁ Ctail Cenergy Ccoef : ℝ)
    (q : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r) (hm : m ≤ n₁ * n₂) (hm_pos : 0 < m)
    (hβ : 2 < β) (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hCtail : 0 < Ctail) (hCenergy : 0 < Cenergy) (hCcoef : 0 < Ccoef)
    (hmax2 : 2 ≤ max n₁ n₂)
    (hqUpper : (q : ℝ) ≤ 2 * (β * Real.log (↑(max n₁ n₂))))
    (hmlow2 : (m : ℝ) ≥ μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))))
    (Omega1 Omega2 : Finset (Fin n₁ × Fin n₂))
    (hNodeIV :
      spectralNorm
          (centeredSamplingFluctuation Omega1
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))))) ≤
        Ctail * Real.sqrt (q : ℝ) *
          (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
          Real.sqrt
            (Cenergy * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (↑(max n₁ n₂)) *
              entrySupNorm
                (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ^ 2))
    (hCoef :
      entrySupNorm
          (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
        Ccoef *
          (Real.sqrt
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
            (((β + 2) * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) :
    spectralNorm
        (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
          Omega1 Omega2 S ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
      (Ctail * Real.sqrt Cenergy * Ccoef * 5) *
        (Real.sqrt (Real.log (↑(max n₁ n₂)) * β) *
          Real.rpow (((↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2) *
            (μ₀ ^ 2 * (r : ℝ))) := by
  classical
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mo : ℝ := (m : ℝ) with hMo
  set mn : ℝ := (↑(min n₁ n₂) : ℝ) with hmn
  set nn : ℝ := (n₁ : ℝ) * (n₂ : ℝ) with hnn
  set logN : ℝ := Real.log N with hlogN
  set p : ℝ := Mo / nn with hp
  set cM := quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S p with hcM
  -- basic positivity
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast (lt_of_lt_of_le hn₁ (Nat.le_max_left _ _))
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast (le_trans hn₁ (Nat.le_max_left _ _))
  have hR1 : 1 ≤ R := by rw [hR]; exact_mod_cast hr
  have hmn_pos : 0 < mn := by rw [hmn]; exact_mod_cast (lt_min hn₁ hn₂)
  have hMo_pos : 0 < Mo := by rw [hMo]; exact_mod_cast hm_pos
  have hnn_pos : 0 < nn := by rw [hnn]; positivity
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hlog_nonneg : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN1
  have hμ₀0 : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₁0 : 0 < μ₁ := lt_of_lt_of_le one_pos hμ₁
  have hnn_eq : nn = N * mn := by
    rw [hN, hmn, hnn]
    have := max_mul_min (n₁) (n₂)
    have hcast : ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
      exact_mod_cast this
    linarith [hcast]
  -- entrySup ≥ 0
  have hES_nonneg :
      0 ≤ entrySupNorm cM := by
    rw [hcM]
    unfold entrySupNorm
    haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
    haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
    apply Real.iSup_nonneg
    intro i; apply Real.iSup_nonneg; intro j; exact abs_nonneg _
  -- Step 1: rep identity + smul
  have hrep :
      quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution Omega1 Omega2 S p =
        (p⁻¹ * (1 - 2 * p)) • centeredSamplingFluctuation Omega1 p cM := by
    rw [hcM]
    exact
      quadratic_neumann_first_index_distinct_centered_decoupled_as_coefficient_fluctuation
        Omega1 Omega2 S p
  have hsmul :
      spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
            Omega1 Omega2 S p) ≤
        |p⁻¹ * (1 - 2 * p)| * spectralNorm (centeredSamplingFluctuation Omega1 p cM) := by
    rw [hrep]; exact spectralNorm_smul_le_abs _ _
  -- Step 2: |a| ≤ nn/M
  have habs : |p⁻¹ * (1 - 2 * p)| ≤ nn / Mo := by
    have := abs_two_prefactor_le_card_div_sample hn₁ hn₂ hm hm_pos
    simpa [hp, hnn, hMo] using this
  -- Step 3: √EnergyBound = √(Cenergy·p·N)·entrySup
  have hsqrtEB :
      Real.sqrt (Cenergy * p * N * entrySupNorm cM ^ 2) =
        Real.sqrt (Cenergy * p * N) * entrySupNorm cM := by
    rw [show Cenergy * p * N * entrySupNorm cM ^ 2
        = (Cenergy * p * N) * entrySupNorm cM ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hES_nonneg]
  -- the coefficient two-term scale (already in folded variables)
  set twoTerm : ℝ :=
    Real.sqrt (((β + 2) * logN) / p) *
        (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn) * (μ₀ * R / mn)) +
      (((β + 2) * logN) / p) *
        (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn) * (μ₀ * R / mn)) with htwoTerm
  have hCoef' : entrySupNorm cM ≤ Ccoef * twoTerm := hCoef
  -- node (iv) bound, with √EnergyBound split
  have hNode' :
      spectralNorm (centeredSamplingFluctuation Omega1 p cM) ≤
        Ctail * Real.sqrt (q : ℝ) * p⁻¹ *
          (Real.sqrt (Cenergy * p * N) * entrySupNorm cM) := by
    have h := hNodeIV
    rw [hsqrtEB] at h
    exact h
  -- abbreviations
  set a : ℝ := p⁻¹ * (1 - 2 * p) with ha
  set sEB : ℝ := Real.sqrt (Cenergy * p * N) with hsEB
  have hsEB_nonneg : 0 ≤ sEB := by rw [hsEB]; exact Real.sqrt_nonneg _
  have hCtail_nonneg : 0 ≤ Ctail := le_of_lt hCtail
  have hsq_nonneg : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  have hpinv_nonneg : 0 ≤ p⁻¹ := by positivity
  -- (1) fluctuation node bound is nonneg on RHS
  have hfluct_nonneg : 0 ≤ spectralNorm (centeredSamplingFluctuation Omega1 p cM) := by
    unfold spectralNorm; exact norm_nonneg _
  -- (2) √q ≤ √(2βlogN)
  have hqbound : Real.sqrt (q : ℝ) ≤ Real.sqrt (2 * (β * logN)) :=
    Real.sqrt_le_sqrt (by simpa [hlogN, mul_comm] using hqUpper)
  -- Chain the conditional bound down to (nn/Mo)·Ctail·√(2βlogN)·p⁻¹·sEB·Ccoef·twoTerm
  -- step: spectralNorm(decoupled) ≤ |a| · nodeRHS
  have hStep1 :
      spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
            Omega1 Omega2 S p) ≤
        (nn / Mo) *
          (Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * twoTerm))) := by
    -- |a|·spectral ≤ (nn/Mo)·(Ctail·√q·p⁻¹·(sEB·(Ccoef·twoTerm)))
    have hnodeES :
        Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * entrySupNorm cM) ≤
          Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * twoTerm)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hCoef' hsEB_nonneg
    have hchain2 :
        spectralNorm (centeredSamplingFluctuation Omega1 p cM) ≤
          Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * twoTerm)) :=
      le_trans (by rw [hsEB] at hNode' ⊢; exact hNode') hnodeES
    calc
      spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
            Omega1 Omega2 S p)
          ≤ |a| * spectralNorm (centeredSamplingFluctuation Omega1 p cM) := hsmul
      _ ≤ (nn / Mo) *
            (Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * twoTerm))) := by
            apply mul_le_mul habs hchain2 hfluct_nonneg (by positivity)
  -- distribute twoTerm and bound √q by √(2βlogN)
  have hΦ3_nonneg :
      0 ≤ Real.sqrt (β * logN) * Real.rpow (N * R / Mo) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R) := by
    have : 0 ≤ Real.rpow (N * R / Mo) ((3 : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
    positivity
  -- the product ≤ condA + condB (raw)
  have hRaw :
      (nn / Mo) * (Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * twoTerm))) ≤
        ((nn / Mo) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * sEB * Ccoef *
            (Real.sqrt (((β + 2) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn) * (μ₀ * R / mn)))) +
          ((nn / Mo) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * sEB * Ccoef *
            ((((β + 2) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn) * (μ₀ * R / mn)))) := by
    have hprefac_nonneg : 0 ≤ (nn / Mo) * Ctail * p⁻¹ * sEB * Ccoef := by positivity
    have htwoTerm_nonneg : 0 ≤ twoTerm := by
      rw [htwoTerm]; positivity
    -- factor and apply √q ≤ √(2βlogN)
    have hexpand :
        (nn / Mo) * (Ctail * Real.sqrt (q : ℝ) * p⁻¹ * (sEB * (Ccoef * twoTerm))) =
          ((nn / Mo) * Ctail * p⁻¹ * sEB * Ccoef) * (Real.sqrt (q : ℝ) * twoTerm) := by
      ring
    have hexpand2 :
        ((nn / Mo) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * sEB * Ccoef *
            (Real.sqrt (((β + 2) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn) * (μ₀ * R / mn)))) +
          ((nn / Mo) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * sEB * Ccoef *
            ((((β + 2) * logN) / p) *
              (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn) * (μ₀ * R / mn)))) =
          ((nn / Mo) * Ctail * p⁻¹ * sEB * Ccoef) *
            (Real.sqrt (2 * (β * logN)) * twoTerm) := by
      rw [htwoTerm]; ring
    rw [hexpand, hexpand2]
    apply mul_le_mul_of_nonneg_left _ hprefac_nonneg
    exact mul_le_mul_of_nonneg_right hqbound htwoTerm_nonneg
  -- apply pieces A and B; note prefactor grouping matches piece helpers
  have hPA := pieceA_le N R Mo mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef
    hN1 hR1 hmn_pos hlog_nonneg hβ hμ₀ hμ₁ hMo_pos hnn_eq hp hCtail hCenergy hCcoef hmlow2
  have hPB := pieceB_le N R Mo mn nn p logN μ₀ μ₁ β Ctail Cenergy Ccoef
    hN1 hR1 hmn_pos hlog_nonneg hβ hμ₀ hμ₁ hMo_pos hnn_eq hp hCtail hCenergy hCcoef hmlow2
  -- pieces are stated with sEB = √(Cenergy·p·N) inlined; fold it
  rw [← hsEB] at hPA hPB
  -- combine
  have hsum :
      ((nn / Mo) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * sEB * Ccoef *
          (Real.sqrt (((β + 2) * logN) / p) *
            (μ₁ * Real.sqrt (R / nn) * Real.sqrt (μ₀ * R / mn) * (μ₀ * R / mn)))) +
        ((nn / Mo) * Ctail * Real.sqrt (2 * (β * logN)) * p⁻¹ * sEB * Ccoef *
          ((((β + 2) * logN) / p) *
            (μ₁ * Real.sqrt (R / nn) * (μ₀ * R / mn) * (μ₀ * R / mn)))) ≤
        (Ctail * Real.sqrt Cenergy * Ccoef * 5) *
          (Real.sqrt (β * logN) * Real.rpow (N * R / Mo) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)) := by
    have hA : _ ≤ _ := hPA
    have hB : _ ≤ _ := hPB
    -- pieceA/B RHS have consts 2 and 3; sum ≤ (5)·Φ3
    have := add_le_add hA hB
    calc
      _ ≤ (Ctail * Real.sqrt Cenergy * Ccoef * 2) *
            (Real.sqrt (β * logN) * Real.rpow (N * R / Mo) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)) +
          (Ctail * Real.sqrt Cenergy * Ccoef * 3) *
            (Real.sqrt (β * logN) * Real.rpow (N * R / Mo) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)) := this
      _ = (Ctail * Real.sqrt Cenergy * Ccoef * 5) *
            (Real.sqrt (β * logN) * Real.rpow (N * R / Mo) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)) := by ring
  -- final chain, normalising √(β logN) = √(logN β) and N*R/Mo = (N*R)/Mo
  have hfinal :
      spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
            Omega1 Omega2 S p) ≤
        (Ctail * Real.sqrt Cenergy * Ccoef * 5) *
          (Real.sqrt (β * logN) * Real.rpow (N * R / Mo) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)) :=
    le_trans hStep1 (le_trans hRaw hsum)
  -- the goal's √ uses `logN * β`; rewrite commutatively
  have hcomm : Real.sqrt (β * logN) = Real.sqrt (logN * β) := by rw [mul_comm]
  rw [hcomm] at hfinal
  -- unfold the folded variables back to the goal's raw casts
  simpa only [hp, hN, hR, hMo, hlogN] using hfinal

end MatrixCompletion

/-- brick 1. -/
theorem solution :
    ∃ Cpair cpair : ℝ, 0 < Cpair ∧ 0 < cpair ∧
      ∀ C' : ℝ, Cpair ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliPairEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega1 Omega2 =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega2 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Cpair *
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
          1 - cpair * Real.rpow (↑(max n₁ n₂)) (-β) := by
  classical
  obtain ⟨Ctail, Cenergy, hCtail, hCenergy, hNodeEvent⟩ :=
    centered_sampling_spectral_event_from_a0_energy_moment
  obtain ⟨Ccoef, ccoef, hCcoef, hccoef, hCoefEvent⟩ :=
    quadratic_neumann_first_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
  refine ⟨max 1 (Ctail * Real.sqrt Cenergy * Ccoef * 5), 1 + ccoef,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), by positivity, ?_⟩
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hmLower
  set Cpair : ℝ := max 1 (Ctail * Real.sqrt Cenergy * Ccoef * 5) with hCpair
  have hC'_one : (1 : ℝ) ≤ C' := le_trans (le_max_left _ _) hC'
  have h5le : Ctail * Real.sqrt Cenergy * Ccoef * 5 ≤ Cpair := le_max_right _ _
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set R : ℝ := (r : ℝ) with hR
  set Mobs : ℝ := (m : ℝ) with hMobs
  set logN : ℝ := Real.log N with hlogN
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hNnat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left _ _)
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hNnat
  have hlog_nonneg : 0 ≤ logN := by rw [hlogN]; exact Real.log_nonneg hN1
  have hμ₀nn : (0 : ℝ) ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁nn : (0 : ℝ) ≤ μ₁ := le_trans zero_le_one hμ₁
  have hβnn : (0 : ℝ) ≤ β := le_of_lt (lt_trans (by norm_num) hβ)
  have hRnn : (0 : ℝ) ≤ R := by rw [hR]; positivity
  have hMobsnn : (0 : ℝ) ≤ Mobs := by rw [hMobs]; positivity
  obtain ⟨hp0, hp1⟩ := sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  -- Φ and its four nonneg summands
  set Φ₁ : ℝ := (μ₀ ^ 2 * μ₁) * Real.sqrt ((N * R * (β * logN)) / Mobs) * ((N * R) / Mobs) ^ 2
    with hΦ₁
  set Φ₂ : ℝ := μ₀ ^ 2 * ((N * R) / Mobs) ^ 2 with hΦ₂
  set Φ₃ : ℝ := Real.sqrt (β * logN) * Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) * (μ₀ ^ 2 * R)
    with hΦ₃
  set Φ₄ : ℝ := Real.rpow ((μ₀ * μ₁ * N * R * (β * logN)) / Mobs) ((3 : ℝ) / 2) with hΦ₄
  set Φ : ℝ := Φ₁ + Φ₂ + Φ₃ + Φ₄ with hΦ
  have hΦ₁nn : 0 ≤ Φ₁ := by rw [hΦ₁]; positivity
  have hΦ₂nn : 0 ≤ Φ₂ := by rw [hΦ₂]; positivity
  have hΦ₃nn : 0 ≤ Φ₃ := by
    rw [hΦ₃]
    have : 0 ≤ Real.rpow ((N * R) / Mobs) ((3 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    positivity
  have hΦ₄nn : 0 ≤ Φ₄ := by rw [hΦ₄]; exact Real.rpow_nonneg (by positivity) _
  have hΦnn : 0 ≤ Φ := by rw [hΦ]; linarith
  -- reduce the goal's let-block to `spectralNorm ≤ Cpair * Φ`
  show bernoulliPairEventProb p
      (fun Omega1 Omega2 =>
        spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
            Omega1 Omega2 S p) ≤ Cpair * Φ) ≥
    1 - (1 + ccoef) * Real.rpow (↑(max n₁ n₂)) (-β)
  -- edge: max n₁ n₂ < 2 ⇒ decoupled ≡ 0 ⇒ event always holds
  by_cases hmax2 : 2 ≤ max n₁ n₂
  · -- main branch
    -- sample lower derivations
    have hK1 : (1 : ℝ) ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
        (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) := by
      have hμ₁sq : (1 : ℝ) ≤ μ₁ ^ 2 := by nlinarith [hμ₁]
      exact le_trans hμ₁sq (le_trans (le_max_left _ _) (le_max_left _ _))
    have hmLower' : (m : ℝ) ≥ C' *
        max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
          (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) *
          N * R * (β * logN) := by
      simpa [hN, hR, hlogN, mul_assoc] using hmLower
    have hR1nat : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast hr
    -- (a) m ≥ β·N·logN
    have hSampleFixed : (m : ℝ) ≥ β * N * logN := by
      have hprod : β * N * logN ≤ C' *
          max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) * N * R * (β * logN) := by
        have hbase : β * N * logN = 1 * 1 * N * 1 * (β * logN) := by ring
        rw [hbase]
        have hmaxge : (1 : ℝ) ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) := by
          have hμ₁sq : (1 : ℝ) ≤ μ₁ ^ 2 := by nlinarith [hμ₁]
          exact le_trans hμ₁sq (le_trans (le_max_left _ _) (le_max_left _ _))
        have hRge : (1 : ℝ) ≤ R := by rw [hR]; exact_mod_cast hr
        gcongr
      linarith [hmLower']
    have hSampleFixed' : (m : ℝ) ≥ β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) := by
      have : β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)) = β * N * logN := by
        rw [hN, hlogN, hN]
      rw [this]; exact hSampleFixed
    -- (b) m ≥ µ₁²·N·r·βlogN
    have hmlow2 : (m : ℝ) ≥ μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) := by
      have hprod : μ₁ ^ 2 * N * R * (β * logN) ≤ C' *
          max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) * N * R * (β * logN) := by
        have hμ₁sqle : μ₁ ^ 2 ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
            (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) :=
          le_trans (le_max_left _ _) (le_max_left _ _)
        have hNRl_nonneg : 0 ≤ N * R * (β * logN) := by rw [hR]; positivity
        calc μ₁ ^ 2 * N * R * (β * logN)
            = μ₁ ^ 2 * (N * R * (β * logN)) := by ring
          _ ≤ (C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))) * (N * R * (β * logN)) := by
              apply mul_le_mul_of_nonneg_right _ hNRl_nonneg
              calc μ₁ ^ 2 ≤ max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                    (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) := hμ₁sqle
                _ = 1 * _ := (one_mul _).symm
                _ ≤ C' * _ := by
                    apply mul_le_mul_of_nonneg_right hC'_one
                    exact le_trans (sq_nonneg μ₁) hμ₁sqle
          _ = _ := by ring
      calc μ₁ ^ 2 * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂)))
          = μ₁ ^ 2 * N * R * (β * logN) := by rw [hN, hR, hlogN, hN]
        _ ≤ _ := hprod
        _ ≤ (m : ℝ) := by simpa [hN, hR, hlogN, mul_assoc] using hmLower'
    have hm_pos : 0 < m := by
      by_contra h
      push_neg at h
      interval_cases m
      · simp at hSampleFixed
        have : 0 < β * N * logN := by
          have hlogpos : 0 < logN := by
            rw [hlogN]; exact Real.log_pos (by rw [hN]; exact_mod_cast hmax2)
          positivity
        linarith [hSampleFixed]
    -- marginal event (coefficient)
    have hMarg := hCoefEvent β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
    -- pair-lift
    have hpair :=
      bernoulli_pair_event_probability_from_marginal_and_conditional_lower_bounds_of_nonneg
        (n₁ := n₁) (n₂ := n₂) p ccoef 1 (Real.rpow (↑(max n₁ n₂)) (-β))
        (fun Omega2 =>
          QuadraticFirstIndexDistinctCenteredCoefficientBound Omega2 S p
            (Ccoef *
              (Real.sqrt (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
                  (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
                  (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))))
        (fun Omega1 Omega2 =>
          spectralNorm
            (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
              Omega1 Omega2 S p) ≤ Cpair * Φ)
        hp0 hp1
        (by
          have : (0 : ℝ) ≤ Real.rpow (↑(max n₁ n₂)) (-β) := Real.rpow_nonneg (by positivity) _
          positivity) ?_ ?_
    · -- conclude: 1 - (1 + ccoef)·scale
      have : (1 : ℝ) + ccoef = 1 + ccoef := rfl
      simpa [add_comm] using hpair
    · -- marginal ≥ 1 - ccoef·scale
      simpa [hp] using hMarg
    · -- conditional
      intro Omega2 hMargGood
      -- node (iv) event over Ω1 for X = coefficient matrix
      have hNode := hNodeEvent β hβ n₁ n₂ m
        (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S p)
        hn₁ hn₂ hm hSampleFixed' hmax2
      obtain ⟨q, hq1, hqLog, hqUpper, hNodeProb⟩ := hNode
      -- coefficient bound holds pointwise on the good Ω2
      have hCoefBound :
          entrySupNorm
              (quadraticFirstIndexDistinctCenteredCoefficientMatrix Omega2 S p) ≤
            Ccoef *
              (Real.sqrt (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
                  (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
                  (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))) := hMargGood
      -- monotone: conditional event holds on the node (iv) event
      refine le_trans hNodeProb ?_
      apply bernoulli_event_probability_mono p _ _ hp0 hp1
      intro Omega1 hΩ1
      -- hΩ1 : CenteredSamplingSpectralBound Ω1 p X threshold
      have hNodeIV := hΩ1
      unfold CenteredSamplingSpectralBound at hNodeIV
      have hcond :=
        conditional_pointwise_bound S β μ₀ μ₁ Ctail Cenergy Ccoef q
          hn₁ hn₂ hr hm hm_pos hβ hμ₀ hμ₁ hCtail hCenergy hCcoef hmax2
          hqUpper hmlow2 Omega1 Omega2 hNodeIV hCoefBound
      -- hcond : spectralNorm(decoupled) ≤ (Ctail·√Cenergy·Ccoef·5)·Φ₃'  (in ↑max form)
      refine le_trans hcond ?_
      -- (Ctail√CeCcoef·5)·Φ₃ ≤ Cpair·Φ
      have hΦ₃eq :
          Real.sqrt (Real.log (↑(max n₁ n₂)) * β) *
              Real.rpow (((↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2) *
                (μ₀ ^ 2 * (r : ℝ)) = Φ₃ := by
        rw [hΦ₃, hN, hR, hMobs, hlogN, hN, mul_comm (Real.log _) β]
      rw [hΦ₃eq]
      calc (Ctail * Real.sqrt Cenergy * Ccoef * 5) * Φ₃
          ≤ Cpair * Φ₃ := mul_le_mul_of_nonneg_right h5le hΦ₃nn
        _ ≤ Cpair * Φ := by
            apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one (le_max_left _ _))
            rw [hΦ]; linarith
  · -- edge: max n₁ n₂ = 1 ⇒ decoupled ≡ 0
    push_neg at hmax2
    have hzero : ∀ (Ω1 Ω2 : Finset (Fin n₁ × Fin n₂)),
        quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution Ω1 Ω2 S p = 0 := by
      intro Ω1 Ω2
      have hn1 : n₁ ≤ 1 := le_trans (Nat.le_max_left n₁ n₂) (Nat.lt_succ_iff.mp hmax2)
      have hn2 : n₂ ≤ 1 := le_trans (Nat.le_max_right n₁ n₂) (Nat.lt_succ_iff.mp hmax2)
      haveI : Subsingleton (Fin n₁ × Fin n₂) := by
        constructor; intro a b
        have : Subsingleton (Fin n₁) := ⟨fun x y => Fin.ext (by omega)⟩
        have : Subsingleton (Fin n₂) := ⟨fun x y => Fin.ext (by omega)⟩
        exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      unfold quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
      refine smul_eq_zero.mpr (Or.inr ?_)
      apply Finset.sum_eq_zero; intro w1 _; apply Finset.sum_eq_zero; intro w2 _
      have : w1 = w2 := Subsingleton.elim _ _
      simp [this]
    have hspec0 : ∀ (Ω1 Ω2 : Finset (Fin n₁ × Fin n₂)),
        spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution Ω1 Ω2 S p) = 0 := by
      intro Ω1 Ω2
      rw [hzero]; unfold spectralNorm; simp
    have hall :
        bernoulliPairEventProb p
            (fun Omega1 Omega2 =>
              spectralNorm
                (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega2 S p) ≤ Cpair * Φ) = 1 := by
      unfold bernoulliPairEventProb
      have hev : ∀ Ω1 Ω2, (spectralNorm
          (quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution Ω1 Ω2 S p) ≤
            Cpair * Φ) := by
        intro Ω1 Ω2; rw [hspec0]
        have : 0 ≤ Cpair * Φ := mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hΦnn
        exact this
      simp only [hev, if_true, mul_one]
      rw [← Finset.sum_mul_sum]
      rw [bernoulliObservationWeight_sum_eq_one]
      ring
    rw [hall]
    have : (0 : ℝ) ≤ (1 + ccoef) * Real.rpow (↑(max n₁ n₂)) (-β) := by
      have : 0 ≤ Real.rpow (↑(max n₁ n₂)) (-β) := Real.rpow_nonneg (by positivity) _
      positivity
    linarith
