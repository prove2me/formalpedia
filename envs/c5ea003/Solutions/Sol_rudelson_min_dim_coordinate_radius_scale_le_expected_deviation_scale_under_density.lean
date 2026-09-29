-- Prove2me | solution 1 for rudelson_min_dim_coordinate_radius_scale_le_expected_deviation_scale_under_density
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T06:05:04.965537+00:00
-- url     : https://prove2.me/submissions/978e5a12-41f6-40d5-96cd-d0514675483f

import Mathlib.Tactic
import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

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

theorem solution
    (Csel Ccoord : ℝ) :
    0 < Csel → 0 < Ccoord →
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥ β * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
          Real.log (↑(max n₁ n₂)) →
        Csel *
            Real.sqrt
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.sqrt
              (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ≤
          tangentSamplingExpectedDeviationScale C μ₀ (max n₁ n₂) r m := by
  intro hCsel hCcoord
  refine ⟨Csel * Real.sqrt Ccoord, ?_, ?_⟩
  · exact mul_pos hCsel (Real.sqrt_pos.2 hCcoord)
  intro β hβ n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hmDense
  let N : ℝ := (max n₁ n₂ : ℕ)
  let mn : ℝ := (min n₁ n₂ : ℕ)
  let nn : ℝ := (n₁ : ℝ) * (n₂ : ℝ)
  let L : ℝ := Real.log N
  have hmin_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hN_nat : 0 < max n₁ n₂ :=
    lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast hN_nat
  have hN_one : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Nat.succ_le_of_lt hN_nat)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg hN_one
  have hmn_pos : 0 < mn := by
    dsimp [mn]
    exact_mod_cast hmin_nat
  have hnn_pos : 0 < nn := by
    dsimp [nn]
    positivity
  have hμ_nonneg : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hβ_pos : 0 < β := by linarith
  have hr_real_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnn_div_min : nn / mn = N := by
    simpa [nn, mn, N] using max_mul_min_cast_div (n₁ := n₁) (n₂ := n₂) hmin_nat
  by_cases hmzero : m = 0
  · subst m
    have hL_zero : L = 0 := by
      have hupper :
          β * μ₀ * N * (r : ℝ) * L ≤ 0 := by
        simpa [N, L] using hmDense
      have hcoeff_pos : 0 < β * μ₀ * N * (r : ℝ) := by
        positivity
      nlinarith
    simp [tangentSamplingExpectedDeviationScale]
  · have hm_pos_nat : 0 < m := Nat.pos_of_ne_zero hmzero
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
    let A : ℝ :=
      Csel *
        Real.sqrt
          (Real.log (↑(max n₁ n₂)) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        Real.sqrt
          (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)))
    let B : ℝ :=
      tangentSamplingExpectedDeviationScale (Csel * Real.sqrt Ccoord)
        μ₀ (max n₁ n₂) r m
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      positivity
    have hB_nonneg : 0 ≤ B := by
      dsimp [B, tangentSamplingExpectedDeviationScale]
      positivity
    have harg1_nonneg :
        0 ≤ Real.log (↑(max n₁ n₂)) /
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
      positivity
    have harg2_nonneg :
        0 ≤ Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by
      positivity
    have hargB_nonneg :
        0 ≤
          (μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
              Real.log (↑(max n₁ n₂))) /
            (m : ℝ) := by
      positivity
    have hsquares : A ^ 2 ≤ B ^ 2 := by
      have hA_sq :
          A ^ 2 =
            Csel ^ 2 *
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
        dsimp [A]
        rw [mul_assoc, mul_pow]
        rw [mul_pow]
        rw [Real.sq_sqrt harg1_nonneg, Real.sq_sqrt harg2_nonneg]
        ring
      have hB_sq :
          B ^ 2 =
            (Csel ^ 2 * Ccoord) *
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                  Real.log (↑(max n₁ n₂))) /
                (m : ℝ)) := by
        dsimp [B, tangentSamplingExpectedDeviationScale]
        rw [mul_pow, mul_pow]
        rw [Real.sq_sqrt hCcoord.le]
        rw [Real.sq_sqrt hargB_nonneg]
      rw [hA_sq, hB_sq]
      have hmain :
          Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) =
            (μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                Real.log (↑(max n₁ n₂))) /
              (m : ℝ) := by
        have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
        have hmn_ne : ((min n₁ n₂ : ℕ) : ℝ) ≠ 0 := ne_of_gt hmn_pos
        have hnn_ne : ((n₁ : ℝ) * (n₂ : ℝ)) ≠ 0 := ne_of_gt hnn_pos
        have hratio :
            ((n₁ : ℝ) * (n₂ : ℝ)) /
                ((min n₁ n₂ : ℕ) : ℝ) =
              ((max n₁ n₂ : ℕ) : ℝ) := by
          simpa using max_mul_min_cast_div (n₁ := n₁) (n₂ := n₂) hmin_nat
        have hprod :
            (n₁ : ℝ) * (n₂ : ℝ) =
              ((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ) := by
          have hnat : max n₁ n₂ * min n₁ n₂ = n₁ * n₂ :=
            max_mul_min n₁ n₂
          exact_mod_cast hnat.symm
        field_simp [hm_ne, hmn_ne, hnn_ne]
        calc
          Real.log (↑(max n₁ n₂)) * (n₁ : ℝ) * (n₂ : ℝ)
              = Real.log (↑(max n₁ n₂)) * ((n₁ : ℝ) * (n₂ : ℝ)) := by
                ring
          _ = Real.log (↑(max n₁ n₂)) *
                (((max n₁ n₂ : ℕ) : ℝ) * ((min n₁ n₂ : ℕ) : ℝ)) := by
                rw [hprod]
          _ = Real.log (↑(max n₁ n₂)) *
                ((min n₁ n₂ : ℕ) : ℝ) * ((max n₁ n₂ : ℕ) : ℝ) := by
                ring
      apply le_of_eq
      calc
        Csel ^ 2 *
              (Real.log (↑(max n₁ n₂)) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)))
            = (Csel ^ 2 * Ccoord) *
                (Real.log (↑(max n₁ n₂)) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) := by
                ring
        _ = (Csel ^ 2 * Ccoord) *
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                  Real.log (↑(max n₁ n₂))) /
                (m : ℝ)) := by
              rw [hmain]
    have habsA : |A| = A := abs_of_nonneg hA_nonneg
    have habsB : |B| = B := abs_of_nonneg hB_nonneg
    have hle_abs : |A| ≤ |B| := (sq_le_sq.mp hsquares)
    have hle : A ≤ B := by simpa [habsA, habsB] using hle_abs
    simpa [A, B] using hle
