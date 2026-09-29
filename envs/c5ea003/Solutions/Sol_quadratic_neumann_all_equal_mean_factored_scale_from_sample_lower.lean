-- Prove2me | solution 1 for quadratic_neumann_all_equal_mean_factored_scale_from_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T18:32:56.203409+00:00
-- url     : https://prove2.me/submissions/1ddee1ca-898d-4f85-81ef-9f80e8643321

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped BigOperators

set_option maxHeartbeats 400000

namespace Prove6d

/-- rpow bridge: write `Real.rpow a b` as `a ^ b`. -/
theorem rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

/-- For `x ≥ 0`, `(x^(4/3))^(3/2) = x^2` (as reals via rpow). -/
theorem pow43_32 (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow (Real.rpow x ((4:ℝ)/3)) ((3:ℝ)/2) = x ^ (2:ℕ) := by
  show (x ^ ((4:ℝ)/3)) ^ ((3:ℝ)/2) = x ^ (2:ℕ)
  rw [← Real.rpow_mul hx, show ((4:ℝ)/3) * ((3:ℝ)/2) = (2:ℝ) by norm_num,
    show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-- `1 ≤ β log n` for `β > 2`, `n ≥ 2`. -/
theorem one_le_beta_log (β n : ℝ) (hβ : 2 < β) (hn : 2 ≤ n) (hlogpos : 0 < Real.log n) :
    (1:ℝ) ≤ β * Real.log n := by
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have h4 : (1:ℝ) < Real.log 4 := by
    have : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_three (by norm_num)
    calc (1:ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) this
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [hlog2n, hlogpos, h4, hlog4]

end Prove6d

open Prove6d in
/-- `quadratic_neumann_all_equal_mean_factored_scale_from_sample_lower`.
Pure scalar scale-absorption: the all-equal Neumann mean term is `O(λ^{-3/2})`. -/
theorem solution
    (Cbase : ℝ) :
    0 < Cbase →
    ∃ Cscale : ℝ, 0 < Cscale ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cbase *
            (|((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
                (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                  2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2))| *
              ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2)) ≤
          Cscale * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCbase
  refine ⟨Cbase, hCbase, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample
  -- abbreviations
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn_def
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  -- basic positivity
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0:ℝ) < μ₀ := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hnpos : (0:ℝ) < n := by
    rw [hn_def]; exact_mod_cast Nat.lt_of_lt_of_le hn₁ (le_max_left _ _)
  have hn1 : (1:ℝ) ≤ n := by
    rw [hn_def]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- max n₁ n₂ ≥ 2 OR = 1
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hsmall | hbig
  · -- max < 2 ⇒ max = 1 ⇒ n₁=n₂=1, m ≤ 1.
    have hn1eq : n₁ = 1 := by
      have := le_max_left n₁ n₂; omega
    have hn2eq : n₂ = 1 := by
      have := le_max_right n₁ n₂; omega
    have hm1 : m ≤ 1 := by rw [hn1eq, hn2eq] at hm; simpa using hm
    -- p = m. case m=0 or m=1
    interval_cases m
    · -- m = 0: p = 0, p⁻² = 0
      have hp0 : p = 0 := by rw [hp_def]; simp
      rw [hp0]
      have hrhs : (0:ℝ) ≤ Cbase * Real.rpow lam (-((3:ℝ)/2)) := by
        have : (0:ℝ) < Real.rpow lam (-((3:ℝ)/2)) := by
          rw [rpow_eq]; exact Real.rpow_pos_of_pos hlam0 _
        positivity
      simp only [inv_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        abs_zero]
      linarith [hrhs]
    · -- m = 1: p = 1, factor 1-3+2 = 0
      have hp1 : p = 1 := by
        rw [hp_def, hn1eq, hn2eq]; norm_num
      rw [hp1]
      have hrhs : (0:ℝ) ≤ Cbase * Real.rpow lam (-((3:ℝ)/2)) := by
        have : (0:ℝ) < Real.rpow lam (-((3:ℝ)/2)) := by
          rw [rpow_eq]; exact Real.rpow_pos_of_pos hlam0 _
        positivity
      have hzero : (1:ℝ) - 3 * 1 + 2 * 1 ^ 2 = 0 := by norm_num
      rw [hzero]
      simp only [mul_zero, abs_zero, zero_mul]
      linarith [hrhs]
  · -- main case: max n₁ n₂ ≥ 2
    have hn2le : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hbig
    have hlogpos : (0:ℝ) < Real.log n := Real.log_pos (by linarith)
    -- L = β log n ≥ 1
    have hLg1 : (1:ℝ) ≤ β * Real.log n := one_le_beta_log β n hβ hn2le hlogpos
    have hLgpos : (0:ℝ) < β * Real.log n := by linarith
    -- lb > 0
    set D : ℝ := Real.rpow (μ₀ * (r:ℝ)) ((4:ℝ)/3) with hD_def
    have hμr1 : (1:ℝ) ≤ μ₀ * (r:ℝ) := by
      have : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      nlinarith
    have hμrpos : (0:ℝ) < μ₀ * (r:ℝ) := by linarith
    have hD1 : (1:ℝ) ≤ D := by
      rw [hD_def, rpow_eq]
      calc (1:ℝ) = (1:ℝ) ^ ((4:ℝ)/3) := by rw [Real.one_rpow]
        _ ≤ (μ₀ * (r:ℝ)) ^ ((4:ℝ)/3) := Real.rpow_le_rpow (by norm_num) hμr1 (by norm_num)
    have hDpos : (0:ℝ) < D := by linarith
    -- rewrite the sample lower bound RHS using D
    have hcombine : Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) = D := by
      rw [hD_def, rpow_eq, rpow_eq, rpow_eq, ← Real.mul_rpow (le_of_lt hμ₀0) (le_of_lt hrR)]
    have hsample' : (m:ℝ) ≥ lam * D * n * (β * Real.log n) := by
      have heq : lam * D * n * (β * Real.log n)
          = lam * Real.rpow μ₀ ((4:ℝ)/3) * n * Real.rpow (r:ℝ) ((4:ℝ)/3) * (β * Real.log n) := by
        rw [← hcombine]; ring
      rw [heq]; exact hsample
    -- lb > 0
    have hlbpos : (0:ℝ) < lam * D * n * (β * Real.log n) := by positivity
    have hmpos : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hlbpos hsample'
    have hppos : (0:ℝ) < p := by rw [hp_def]; positivity
    have hple1 : p ≤ 1 := by
      rw [hp_def, div_le_one (by positivity)]
      have : (m:ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
      push_cast at this; linarith
    -- |p⁻² (1-3p+2p²)| ≤ p⁻²  since |1-3p+2p²| ≤ 1 for p∈[0,1]
    have hfactor : |((1:ℝ) - 3*p + 2*p^2)| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg p, sq_nonneg (1-p), hppos, hple1]
    have hpinv2pos : (0:ℝ) < (p⁻¹)^2 := by positivity
    have hinner_le : |((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2))| ≤ (p⁻¹)^2 := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hpinv2pos)]
      calc (p⁻¹)^2 * |(1 - 3*p + 2*p^2)| ≤ (p⁻¹)^2 * 1 := by
              apply mul_le_mul_of_nonneg_left hfactor (le_of_lt hpinv2pos)
        _ = (p⁻¹)^2 := by ring
    -- (μ₀ r/n)^2 = (μ₀ r)^2 / n^2
    have hμr_sq : (μ₀ * (r:ℝ) / n) ^ 2 = (μ₀ * (r:ℝ))^2 / n^2 := by
      rw [div_pow]
    -- p⁻¹ = n₁n₂/m ≤ n²/lb
    have hpinv_le : p⁻¹ ≤ n^2 / (lam * D * n * (β * Real.log n)) := by
      rw [hp_def, inv_div]
      apply div_le_div₀
      · positivity
      · -- n₁ n₂ ≤ n²
        rw [hn_def]
        have h1 : (n₁:ℝ) ≤ (↑(max n₁ n₂):ℝ) := by exact_mod_cast le_max_left _ _
        have h2 : (n₂:ℝ) ≤ (↑(max n₁ n₂):ℝ) := by exact_mod_cast le_max_right _ _
        nlinarith [hn₁R, hn₂R]
      · exact hlbpos
      · exact hsample'
    -- now assemble: LHS ≤ Cbase * (p⁻¹)^2 * (μ₀r)^2/n^2
    have hLHS_step1 :
        Cbase * (|((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2))| * (μ₀ * (r:ℝ) / n) ^ 2)
          ≤ Cbase * ((p⁻¹)^2 * ((μ₀ * (r:ℝ))^2 / n^2)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCbase)
      rw [hμr_sq]
      apply mul_le_mul_of_nonneg_right hinner_le (by positivity)
    -- bound (p⁻¹)^2
    have hpinv2_le : (p⁻¹)^2 ≤ (n^2 / (lam * D * n * (β * Real.log n)))^2 := by
      apply pow_le_pow_left₀ (le_of_lt (by positivity)) hpinv_le
    -- combine into the final scalar inequality
    -- target form: Cbase * ((p⁻¹)^2 * ((μ₀r)^2/n^2)) ≤ Cbase * lam^(-3/2)
    -- (n²/(lam D n L))² * (μ₀r)²/n² = n⁴/(lam² D² n² L²) * (μ₀r)²/n²
    --   = (μ₀r)²/(lam² D² L²)   [since n⁴/n²/n² = 1]
    -- (μ₀r)² = (D)^(3/2)  via pow43_32
    have hμr2_eq : (μ₀ * (r:ℝ))^2 = Real.rpow D ((3:ℝ)/2) := by
      rw [hD_def, pow43_32 (μ₀ * (r:ℝ)) (le_of_lt hμrpos)]
    -- key algebraic bound
    have hkey :
        ((n^2 / (lam * D * n * (β * Real.log n)))^2 * ((μ₀ * (r:ℝ))^2 / n^2))
          ≤ Real.rpow lam (-((3:ℝ)/2)) := by
      -- first simplify the LHS exactly
      have hsimp :
          (n^2 / (lam * D * n * (β * Real.log n)))^2 * ((μ₀ * (r:ℝ))^2 / n^2)
            = (μ₀ * (r:ℝ))^2 / (lam^2 * D^2 * (β * Real.log n)^2) := by
        field_simp
        try ring
      rw [hsimp, hμr2_eq]
      -- Real.rpow D (3/2) / (lam² D² L²) ≤ lam^(-3/2)
      -- Real.rpow D (3/2) / D² = Real.rpow D (-1/2) ≤ 1
      have hDratio : Real.rpow D ((3:ℝ)/2) / Real.rpow D 2 = Real.rpow D (-(1:ℝ)/2) := by
        rw [rpow_eq, rpow_eq, rpow_eq, ← Real.rpow_sub hDpos]; norm_num
      have hD2eq : (D:ℝ)^2 = Real.rpow D 2 := (Real.rpow_two D).symm
      have hDhalf_le : Real.rpow D (-(1:ℝ)/2) ≤ 1 := by
        rw [rpow_eq, show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hDpos),
          inv_le_one_iff₀]
        right
        calc (1:ℝ) = (1:ℝ) ^ ((1:ℝ)/2) := by rw [Real.one_rpow]
          _ ≤ D ^ ((1:ℝ)/2) := Real.rpow_le_rpow (by norm_num) hD1 (by norm_num)
      -- lam^(-3/2) ≥ lam^(-2)
      have hlam_pow : Real.rpow lam (-(2:ℝ)) ≤ Real.rpow lam (-((3:ℝ)/2)) := by
        rw [rpow_eq, rpow_eq]
        apply Real.rpow_le_rpow_of_exponent_le hlam (by norm_num)
      -- now: numerator/(lam² D² L²) = (Real.rpow D (3/2)/D²)/(lam² L²) = Real.rpow D (-1/2)/(lam² L²)
      have hLg2_1 : (1:ℝ) ≤ (β * Real.log n)^2 := by nlinarith [hLg1, hLgpos]
      have hlamneg2 : Real.rpow lam (-(2:ℝ)) = 1 / lam^2 := by
        show lam ^ (-(2:ℝ)) = 1 / lam^2
        rw [Real.rpow_neg (le_of_lt hlam0), Real.rpow_two, one_div]
      calc Real.rpow D ((3:ℝ)/2) / (lam^2 * D^2 * (β * Real.log n)^2)
          = (Real.rpow D ((3:ℝ)/2) / Real.rpow D 2) * (1 / (lam^2 * (β * Real.log n)^2)) := by
            rw [hD2eq]; field_simp; try ring
        _ = Real.rpow D (-(1:ℝ)/2) * (1 / (lam^2 * (β * Real.log n)^2)) := by rw [hDratio]
        _ ≤ 1 * (1 / (lam^2 * 1)) := by
            apply mul_le_mul hDhalf_le _ (by positivity) (by norm_num)
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            nlinarith [hLg2_1, sq_nonneg lam, hlam0]
        _ = 1 / lam^2 := by ring
        _ = Real.rpow lam (-(2:ℝ)) := by rw [hlamneg2]
        _ ≤ Real.rpow lam (-((3:ℝ)/2)) := hlam_pow
    -- final chain
    calc Cbase *
            (|((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
                (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                  2 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2))| *
              ((μ₀ * (r : ℝ) / (↑(max n₁ n₂))) ^ 2))
        = Cbase * (|((p⁻¹) ^ 2 * (1 - 3 * p + 2 * p ^ 2))| * (μ₀ * (r:ℝ) / n) ^ 2) := by
          rw [← hp_def, ← hn_def]
      _ ≤ Cbase * ((p⁻¹)^2 * ((μ₀ * (r:ℝ))^2 / n^2)) := hLHS_step1
      _ ≤ Cbase * ((n^2 / (lam * D * n * (β * Real.log n)))^2 * ((μ₀ * (r:ℝ))^2 / n^2)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCbase)
          apply mul_le_mul_of_nonneg_right hpinv2_le (by positivity)
      _ ≤ Cbase * Real.rpow lam (-((3:ℝ)/2)) := by
          apply mul_le_mul_of_nonneg_left hkey (le_of_lt hCbase)
