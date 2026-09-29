-- Prove2me | solution 1 for quadratic_base_scalar_bernstein_natural_scale_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T19:15:04.759426+00:00
-- url     : https://prove2.me/submissions/b249f775-b56f-4787-8110-6ed80f79fce9

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped BigOperators

set_option maxHeartbeats 400000

namespace Provef4

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

/-- `(W^(3/2))^2 = W^3` for `W ≥ 0`. -/
theorem rpow32_sq (W : ℝ) (hW : 0 ≤ W) : (Real.rpow W ((3:ℝ)/2))^2 = W^3 := by
  have e1 : (Real.rpow W ((3:ℝ)/2))^2 = (W ^ ((3:ℝ)/2)) ^ (2:ℕ) := rfl
  rw [e1, ← Real.rpow_natCast (W ^ ((3:ℝ)/2)) 2, ← Real.rpow_mul hW]
  norm_num

theorem sqrt_sq_nonneg (a : ℝ) (ha : 0 ≤ a) : (Real.sqrt a)^2 = a := Real.sq_sqrt ha

/-- Term-1 squared polynomial inequality (plain vars, no lets — fast). -/
theorem term1_poly (L x n m n1 n2 : ℝ) (hL:0<L)(hx:0<x)(hn:0<n)(hm:0<m)(hn1:0<n1)(hn2:0<n2)
    (hn1n2: n1*n2 ≤ n^2)(hmle: m ≤ n^2) :
    L * (n1 * n2) / m * (x/n)^3 ≤ L * (x*n/m)^3 := by
  have key : L * (x*n/m)^3 - L * (n1 * n2) / m * (x/n)^3
      = (L * x^3 / (m^3 * n^3)) * (n^6 - n1*n2*m^2) := by field_simp
  have hm2 : m^2 ≤ n^4 := by nlinarith [hmle, hm, hn]
  have hfac : 0 ≤ n^6 - n1*n2*m^2 := by
    have : n1*n2*m^2 ≤ n^2 * n^4 := mul_le_mul hn1n2 hm2 (by positivity) (by positivity)
    nlinarith [this]
  nlinarith [key, mul_nonneg (by positivity : (0:ℝ) ≤ L * x^3 / (m^3*n^3)) hfac]

/-- Term-2 squared polynomial inequality (plain vars, no lets — fast). -/
theorem term2_poly (L x n m n1 n2 : ℝ) (hL:0<L)(hx:0<x)(hn:0<n)(hm:0<m)(hn1:0<n1)(hn2:0<n2)
    (hn1n2: n1*n2 ≤ n^2)(hmle: m ≤ n^2)(hxL: x*L ≤ n) :
    (L * (n1 * n2) / m * (x/n)^2)^2 ≤ L * (x*n/m)^3 := by
  have key : L * (x*n/m)^3 - (L * (n1 * n2) / m * (x/n)^2)^2
      = (L * x^3 / (m^3 * n^4)) * (n^7 - L*(n1*n2)^2*m*x) := by field_simp
  have h1 : (n1*n2)^2 ≤ n^4 := by nlinarith [hn1n2, mul_pos hn1 hn2, hn]
  have hfac : 0 ≤ n^7 - L*(n1*n2)^2*m*x := by
    have hb1 : (n1*n2)^2 * m ≤ n^4 * n^2 := by nlinarith [h1, hmle, mul_pos hn1 hn2, hm, hn]
    have hb2 : ((n1*n2)^2 * m) * (x*L) ≤ (n^4 * n^2) * n :=
      mul_le_mul hb1 hxL (by positivity) (by positivity)
    nlinarith [hb2]
  nlinarith [key, mul_nonneg (by positivity : (0:ℝ) ≤ L * x^3 / (m^3*n^4)) hfac]

end Provef4

open Provef4 in
/-- `quadratic_base_scalar_bernstein_natural_scale_absorption`. -/
theorem solution
    (Cbern Centry Cfro : ℝ) :
    0 < Cbern → 0 < Centry → 0 < Cfro →
    ∃ Cpoint : ℝ, 0 < Cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cbern *
            (Real.sqrt
                ((β * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
                Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2)) +
              ((β * Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Centry * μ₀ ^ 2 *
                (((r : ℝ) / (↑(max n₁ n₂))) ^ 2))) ≤
          Cpoint *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
              Real.rpow
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                ((3 : ℝ) / 2) := by
  intro hCbern hCentry hCfro
  refine ⟨Cbern * (Cfro + Centry), by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample
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
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hsmall | hbig
  · -- n=1: log n = 0 ⇒ bracket = 0
    have hmaxeq : max n₁ n₂ = 1 := by have := le_max_left n₁ n₂; omega
    have hnval : n = 1 := by rw [hn_def, hmaxeq]; norm_num
    have hLval : L = 0 := by rw [hL_def, hnval]; simp
    rw [hLval]
    have hrhs0 : (0:ℝ) ≤ Cbern * (Cfro + Centry) *
        Real.sqrt (0:ℝ) * Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3:ℝ)/2) := by
      rw [Real.sqrt_zero]; simp
    simp only [zero_div, Real.sqrt_zero, zero_mul, zero_add, mul_zero]
    positivity
  · -- main case
    have hn2le : (2:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast hbig
    have hnpos : (0:ℝ) < n := by linarith
    have hlogpos : (0:ℝ) < Real.log n := Real.log_pos (by linarith)
    have hL1 : (1:ℝ) ≤ L := by rw [hL_def]; exact one_le_beta_log β n hβ hn2le hlogpos
    have hLpos : (0:ℝ) < L := by linarith
    set D : ℝ := Real.rpow x ((4:ℝ)/3) with hD_def
    have hcombine : Real.rpow μ₀ ((4:ℝ)/3) * Real.rpow (r:ℝ) ((4:ℝ)/3) = D := by
      rw [hD_def, hx_def, rpow_eq, rpow_eq, rpow_eq, ← Real.mul_rpow (le_of_lt hμ₀0) (le_of_lt hrR)]
    have hD1 : (1:ℝ) ≤ D := by
      rw [hD_def, rpow_eq]
      calc (1:ℝ) = (1:ℝ) ^ ((4:ℝ)/3) := by rw [Real.one_rpow]
        _ ≤ x ^ ((4:ℝ)/3) := Real.rpow_le_rpow (by norm_num) hx1 (by norm_num)
    have hDpos : (0:ℝ) < D := by linarith
    have hxleD : x ≤ D := by
      rw [hD_def, rpow_eq]
      calc x = x ^ (1:ℝ) := by rw [Real.rpow_one]
        _ ≤ x ^ ((4:ℝ)/3) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hsample' : (m:ℝ) ≥ lam * D * n * L := by
      have heq : lam * D * n * L
          = lam * Real.rpow μ₀ ((4:ℝ)/3) * n * Real.rpow (r:ℝ) ((4:ℝ)/3) * (β * Real.log n) := by
        rw [← hcombine, hL_def]; ring
      rw [heq, ← hn_def] at *; exact hsample
    have hlbpos : (0:ℝ) < lam * D * n * L := by positivity
    have hmpos : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hlbpos hsample'
    have hmle : (m:ℝ) ≤ n^2 := by
      have h1 : (n₁:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_left _ _
      have h2 : (n₂:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_right _ _
      have : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hm
      nlinarith [this, hn₁R, hn₂R, h1, h2]
    have hn1n2 : (n₁:ℝ) * (n₂:ℝ) ≤ n^2 := by
      have h1 : (n₁:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_left _ _
      have h2 : (n₂:ℝ) ≤ n := by rw [hn_def]; exact_mod_cast le_max_right _ _
      nlinarith [hn₁R, hn₂R]
    -- feasibility: D * L ≤ n
    have hDLn : D * L ≤ n := by
      -- lam D n L ≤ m ≤ n² and lam ≥ 1 ⇒ D n L ≤ n² ⇒ D L ≤ n
      have h1 : D * n * L ≤ n^2 := by
        have hge : lam * D * n * L ≤ n^2 := le_trans hsample' hmle
        nlinarith [hge, hlam, hDpos, hnpos, hLpos, mul_nonneg (mul_nonneg (le_of_lt hDpos) (le_of_lt hnpos)) (le_of_lt hLpos)]
      -- D n L ≤ n² ⇒ (D L) n ≤ n*n ⇒ D L ≤ n
      have h2 : (D * L) * n ≤ n * n := by nlinarith [h1]
      exact le_of_mul_le_mul_right h2 hnpos
    -- abbreviations
    set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
    have hppos : (0:ℝ) < p := by rw [hp_def]; positivity
    -- L/p = L * (n₁n₂)/m
    have hLp_eq : L / p = L * ((n₁:ℝ) * (n₂:ℝ)) / m := by
      rw [hp_def]; field_simp
    -- W = μ₀ n r / m = x n / m
    set W : ℝ := (μ₀ * n * (r:ℝ)) / (m:ℝ) with hW_def
    have hWeq : W = x * n / m := by rw [hW_def, hx_def]; ring
    have hWpos : (0:ℝ) < W := by rw [hWeq]; positivity
    -- RHS = Cpoint * √L * W^(3/2); set Rt := √L * W^(3/2)
    have hsqrtL_pos : (0:ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hLpos
    have hW32_pos : (0:ℝ) < Real.rpow W ((3:ℝ)/2) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hWpos _
    -- ===== TERM 1 ≤ Cfro * √L * W^(3/2) =====
    have hterm1 :
        Real.sqrt (L / p) * (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2))
          ≤ Cfro * (Real.sqrt L * Real.rpow W ((3:ℝ)/2)) := by
      -- merge μ₀^(3/2)(r/n)^(3/2) = (x/n)^(3/2)
      have hmerge : Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)
          = Real.rpow (x/n) ((3:ℝ)/2) := by
        rw [hx_def, rpow_eq, rpow_eq, rpow_eq, ← Real.mul_rpow (le_of_lt hμ₀0) (by positivity),
          mul_div_assoc]
      have hxn_pos : (0:ℝ) < x / n := by positivity
      have hxn32_pos : (0:ℝ) < Real.rpow (x/n) ((3:ℝ)/2) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hxn_pos _
      rw [show Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)
          = Cfro * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)) by ring, hmerge]
      rw [show Real.sqrt (L/p) * (Cfro * Real.rpow (x/n) ((3:ℝ)/2))
          = Cfro * (Real.sqrt (L/p) * Real.rpow (x/n) ((3:ℝ)/2)) by ring]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCfro)
      -- compare via squares: both sides ≥ 0
      have hLHSnn : (0:ℝ) ≤ Real.sqrt (L/p) * Real.rpow (x/n) ((3:ℝ)/2) := by positivity
      have hRHSnn : (0:ℝ) ≤ Real.sqrt L * Real.rpow W ((3:ℝ)/2) := by positivity
      rw [← Real.sqrt_sq hRHSnn, ← Real.sqrt_sq hLHSnn]
      apply Real.sqrt_le_sqrt
      -- (√(L/p) (x/n)^(3/2))² ≤ (√L W^(3/2))²
      rw [mul_pow, mul_pow, sqrt_sq_nonneg _ (le_of_lt (by positivity : (0:ℝ) < L/p)),
        sqrt_sq_nonneg _ (le_of_lt hLpos), rpow32_sq _ (le_of_lt hxn_pos), rpow32_sq _ (le_of_lt hWpos)]
      -- (L/p) * (x/n)³ ≤ L * W³
      rw [hLp_eq, hWeq]
      exact term1_poly L x n m (n₁:ℝ) (n₂:ℝ) hLpos hxpos hnpos hmpos hn₁R hn₂R hn1n2 hmle
    -- ===== TERM 2 ≤ Centry * √L * W^(3/2) =====
    -- need x*L ≤ n
    have hxL : x * L ≤ n := by
      calc x * L ≤ D * L := by nlinarith [hxleD, hLpos, hL1]
        _ ≤ n := hDLn
    have hterm2 :
        (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2))
          ≤ Centry * (Real.sqrt L * Real.rpow W ((3:ℝ)/2)) := by
      -- μ₀²(r/n)² = (x/n)²
      have hmul2 : μ₀ ^ 2 * (((r:ℝ)/n) ^ 2) = (x/n)^2 := by rw [hx_def]; rw [div_pow]; ring
      rw [show Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2) = Centry * (μ₀ ^ 2 * (((r:ℝ)/n) ^ 2)) by ring, hmul2]
      rw [show (L/p) * (Centry * (x/n)^2) = Centry * ((L/p) * (x/n)^2) by ring]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCentry)
      -- (L/p)(x/n)² ≤ √L W^(3/2)  via squares
      have hLHSnn : (0:ℝ) ≤ (L/p) * (x/n)^2 := by positivity
      have hRHSnn : (0:ℝ) ≤ Real.sqrt L * Real.rpow W ((3:ℝ)/2) := by positivity
      rw [← Real.sqrt_sq hRHSnn, ← Real.sqrt_sq hLHSnn]
      apply Real.sqrt_le_sqrt
      have hrhs_eq : (Real.sqrt L * Real.rpow W ((3:ℝ)/2))^2 = L * W^3 := by
        rw [mul_pow, sqrt_sq_nonneg _ (le_of_lt hLpos), rpow32_sq _ (le_of_lt hWpos)]
      rw [hrhs_eq]
      -- ((L/p)(x/n)²)² ≤ L * W³
      rw [hLp_eq, hWeq]
      exact term2_poly L x n m (n₁:ℝ) (n₂:ℝ) hLpos hxpos hnpos hmpos hn₁R hn₂R hn1n2 hmle hxL
    -- ===== ASSEMBLE =====
    have hbracket :
        (Real.sqrt (L / p) *
            (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)) +
          (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2)))
          ≤ (Cfro + Centry) * (Real.sqrt L * Real.rpow W ((3:ℝ)/2)) := by
      calc _ ≤ Cfro * (Real.sqrt L * Real.rpow W ((3:ℝ)/2))
                + Centry * (Real.sqrt L * Real.rpow W ((3:ℝ)/2)) := add_le_add hterm1 hterm2
        _ = (Cfro + Centry) * (Real.sqrt L * Real.rpow W ((3:ℝ)/2)) := by ring
    -- goal is in n,L,p,W form; chain
    have hfinal := mul_le_mul_of_nonneg_left hbracket (le_of_lt hCbern)
    calc Cbern *
            (Real.sqrt (L / p) *
              (Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/n) ((3:ℝ)/2)) +
            (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ)/n) ^ 2)))
        ≤ Cbern * ((Cfro + Centry) * (Real.sqrt L * Real.rpow W ((3:ℝ)/2))) := hfinal
      _ = Cbern * (Cfro + Centry) * Real.sqrt L * Real.rpow W ((3:ℝ)/2) := by ring
