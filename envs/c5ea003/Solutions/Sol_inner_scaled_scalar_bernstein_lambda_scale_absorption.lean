-- Prove2me | solution 1 for inner_scaled_scalar_bernstein_lambda_scale_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T19:22:50.452079+00:00
-- url     : https://prove2.me/submissions/b662107f-64eb-48c1-befe-b71b6093cd70

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped BigOperators

set_option maxHeartbeats 400000

namespace Prove10855

theorem rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

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

/-- `lam^(-1/2) = 1/√lam`. -/
theorem rpow_neg_half (lam : ℝ) (h : 0 < lam) : Real.rpow lam (-((1:ℝ)/2)) = 1 / Real.sqrt lam := by
  rw [Real.sqrt_eq_rpow]
  show lam ^ (-((1:ℝ)/2)) = 1 / lam ^ ((1:ℝ)/2)
  rw [Real.rpow_neg (le_of_lt h), inv_eq_one_div]

/-- `lam^(-1) = lam^(-1/2) * lam^(-1/2)`. -/
theorem rpow_neg_one_split (lam : ℝ) (h : 0 < lam) :
    Real.rpow lam (-1) = Real.rpow lam (-((1:ℝ)/2)) * Real.rpow lam (-((1:ℝ)/2)) := by
  show lam ^ (-1 : ℝ) = lam ^ (-((1:ℝ)/2)) * lam ^ (-((1:ℝ)/2))
  rw [← Real.rpow_add h]; norm_num

end Prove10855

open Prove10855 in
/-- `inner_scaled_scalar_bernstein_lambda_scale_absorption`. -/
theorem solution
    (Cbern Centry Cfro : ℝ) :
    0 < Cbern → 0 < Centry → 0 < Cfro →
    ∃ Cpoint : ℝ, 0 < Cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ Cinner : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 0 < Cinner →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cbern *
            (Real.sqrt
                ((β * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
                Real.sqrt (μ₀ * ((r : ℝ) / (↑(max n₁ n₂))))) +
              ((β * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Centry * (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) *
                μ₀ * ((r : ℝ) / (↑(max n₁ n₂))))) ≤
          (Cpoint * Cinner) * Real.rpow lam (-1) := by
  intro hCbern hCentry hCfro
  refine ⟨Cbern * (Cfro + Centry), by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ Cinner hn₁ hn₂ hr hm hμ₀ hCinner hsample
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn_def
  set L : ℝ := β * Real.log n with hL_def
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0:ℝ) < μ₀ := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  set x : ℝ := μ₀ * (r:ℝ) with hx_def
  have hx1 : (1:ℝ) ≤ x := by rw [hx_def]; nlinarith
  have hxpos : (0:ℝ) < x := by linarith
  -- lam^(-1/2) value
  have hlh : Real.rpow lam (-((1:ℝ)/2)) = 1 / Real.sqrt lam := rpow_neg_half lam hlam0
  have hsqrtlam_pos : (0:ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hlh_pos : (0:ℝ) < Real.rpow lam (-((1:ℝ)/2)) := by rw [hlh]; positivity
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hsmall | hbig
  · -- n=1: log n = 0 ⇒ bracket = 0
    have hmaxeq : max n₁ n₂ = 1 := by have := le_max_left n₁ n₂; omega
    have hnval : n = 1 := by rw [hn_def, hmaxeq]; norm_num
    have hLval : L = 0 := by rw [hL_def, hnval]; simp
    rw [hLval]
    have hrhs0 : (0:ℝ) ≤ (Cbern * (Cfro + Centry) * Cinner) * Real.rpow lam (-1) := by
      have : (0:ℝ) < Real.rpow lam (-1) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hlam0 _
      positivity
    simp only [zero_div, Real.sqrt_zero, zero_mul, zero_add, mul_zero]
    linarith [hrhs0]
  · -- main case
    have hn2le : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hbig
    have hnpos : (0:ℝ) < n := by linarith
    have hlogpos : (0:ℝ) < Real.log n := Real.log_pos (by linarith)
    have hL1 : (1:ℝ) ≤ L := by rw [hL_def]; exact one_le_beta_log β n hβ hn2le hlogpos
    have hLpos : (0:ℝ) < L := by linarith
    set D : ℝ := Real.rpow x ((4:ℝ)/3) with hD_def
    have hcombine : Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) = D := by
      rw [hD_def, hx_def, rpow_eq, rpow_eq, rpow_eq, ← Real.mul_rpow (le_of_lt hμ₀0) (le_of_lt hrR)]
    have hxleD : x ≤ D := by
      rw [hD_def, rpow_eq]
      calc x = x ^ (1:ℝ) := by rw [Real.rpow_one]
        _ ≤ x ^ ((4:ℝ)/3) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hDpos : (0:ℝ) < D := by linarith
    have hsample' : (m:ℝ) ≥ lam * D * n * L := by
      have heq : lam * D * n * L
          = lam * Real.rpow μ₀ ((4:ℝ)/3) * n * Real.rpow (r:ℝ) ((4:ℝ)/3) * (β * Real.log n) := by
        rw [← hcombine, hL_def]; ring
      rw [heq, ← hn_def] at *; exact hsample
    have hlbpos : (0:ℝ) < lam * D * n * L := by positivity
    have hmpos : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hlbpos hsample'
    have hn1n2 : (n₁:ℝ) * (n₂:ℝ) ≤ n^2 := by
      have h1 : (n₁:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_left _ _
      have h2 : (n₂:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_right _ _
      nlinarith [hn₁R, hn₂R]
    set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
    have hppos : (0:ℝ) < p := by rw [hp_def]; positivity
    have hLp_eq : L / p = L * ((n₁:ℝ) * (n₂:ℝ)) / m := by rw [hp_def]; field_simp
    -- KEY: (L/p) ≤ n/(lam*D)
    have hLp_le : L / p ≤ n / (lam * D) := by
      rw [hLp_eq, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsample', hn1n2, hLpos, hDpos, hlam0, hnpos, hn₁R, hn₂R,
        mul_pos hlam0 hDpos, mul_pos hLpos (mul_pos hlam0 hDpos)]
    -- KEY2: (L/p)*(x/n) ≤ 1/lam
    have hkey : (L / p) * (x / n) ≤ 1 / lam := by
      calc (L / p) * (x / n) ≤ (n / (lam * D)) * (x / n) :=
            mul_le_mul_of_nonneg_right hLp_le (by positivity)
        _ = x / (lam * D) := by field_simp
        _ ≤ x / (lam * x) := by
            apply div_le_div_of_nonneg_left (le_of_lt hxpos) (by positivity)
            nlinarith [hxleD, hlam, hlam0, hxpos]
        _ = 1 / lam := by rw [mul_comm lam x, ← div_div, div_self (ne_of_gt hxpos)]
    have hLp_pos : (0:ℝ) < L / p := by positivity
    -- ===== TERM 1: √(L/p)*√(μ₀ r/n) ≤ lam^(-1/2) =====
    -- √(μ₀ r/n) = √(x/n)
    have hμrn : μ₀ * ((r:ℝ)/n) = x / n := by rw [hx_def]; ring
    have hT1 : Real.sqrt (L/p) * Real.sqrt (μ₀ * ((r:ℝ)/n)) ≤ Real.rpow lam (-((1:ℝ)/2)) := by
      rw [hμrn, ← Real.sqrt_mul (le_of_lt hLp_pos), hlh]
      have hrhs : (1:ℝ)/Real.sqrt lam = Real.sqrt (1/lam) := by
        rw [one_div, one_div, ← Real.sqrt_inv]
      rw [hrhs]
      exact Real.sqrt_le_sqrt hkey
    -- ===== TERM 2: (L/p)*(μ₀ r/n) ≤ lam^(-1/2) =====
    have hT2 : (L/p) * (μ₀ * ((r:ℝ)/n)) ≤ Real.rpow lam (-((1:ℝ)/2)) := by
      rw [hμrn, hlh]
      -- (L/p)(x/n) ≤ 1/lam ≤ 1/√lam
      calc (L/p) * (x/n) ≤ 1/lam := hkey
        _ ≤ 1/Real.sqrt lam := by
            apply div_le_div_of_nonneg_left (by norm_num) hsqrtlam_pos
            calc Real.sqrt lam ≤ Real.sqrt (lam*lam) := by
                  apply Real.sqrt_le_sqrt; nlinarith [hlam, hlam0]
              _ = lam := by rw [Real.sqrt_mul_self (le_of_lt hlam0)]
    -- ===== ASSEMBLE =====
    -- LHS = Cbern*(√(L/p)*(Cfro*(Cinner*λ^{-1/2})*√(μ₀r/n)) + (L/p)*(Centry*(Cinner*λ^{-1/2})*μ₀*(r/n)))
    -- Term1_full = Cinner*λ^{-1/2}*Cfro*(√(L/p)*√(μ₀r/n)) ≤ Cinner*λ^{-1/2}*Cfro*λ^{-1/2}
    have hci_lh_nn : (0:ℝ) ≤ Cinner * Real.rpow lam (-((1:ℝ)/2)) := by positivity
    have hT1full :
        Real.sqrt (L/p) * (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) *
          Real.sqrt (μ₀ * ((r:ℝ)/n)))
          ≤ Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * Real.rpow lam (-((1:ℝ)/2)) := by
      rw [show Real.sqrt (L/p) * (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) *
            Real.sqrt (μ₀ * ((r:ℝ)/n)))
          = (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2)))) *
            (Real.sqrt (L/p) * Real.sqrt (μ₀ * ((r:ℝ)/n))) by ring]
      apply mul_le_mul_of_nonneg_left hT1 (by positivity)
    have hT2full :
        (L/p) * (Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * μ₀ * ((r:ℝ)/n))
          ≤ Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * Real.rpow lam (-((1:ℝ)/2)) := by
      rw [show (L/p) * (Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * μ₀ * ((r:ℝ)/n))
          = (Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2)))) *
            ((L/p) * (μ₀ * ((r:ℝ)/n))) by ring]
      apply mul_le_mul_of_nonneg_left hT2 (by positivity)
    -- λ^{-1/2}·λ^{-1/2} = λ^{-1}
    have hlh2 : Real.rpow lam (-((1:ℝ)/2)) * Real.rpow lam (-((1:ℝ)/2)) = Real.rpow lam (-1) :=
      (rpow_neg_one_split lam hlam0).symm
    calc Cbern *
            (Real.sqrt (L/p) * (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) *
              Real.sqrt (μ₀ * ((r:ℝ)/n))) +
            (L/p) * (Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * μ₀ * ((r:ℝ)/n)))
        ≤ Cbern * (Cfro * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * Real.rpow lam (-((1:ℝ)/2)) +
            Centry * (Cinner * Real.rpow lam (-((1:ℝ)/2))) * Real.rpow lam (-((1:ℝ)/2))) := by
          apply mul_le_mul_of_nonneg_left (add_le_add hT1full hT2full) (le_of_lt hCbern)
      _ = (Cbern * (Cfro + Centry) * Cinner) * Real.rpow lam (-1) := by
          rw [← hlh2]; ring
