-- Prove2me | solution 1 for linear_neumann_centered_sampling_prefactor_absorbed_by_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T19:28:14.084317+00:00
-- url     : https://prove2.me/submissions/ee407149-d352-4a68-8cd4-bc88d1447ddc

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped BigOperators

set_option maxHeartbeats 400000

namespace Provedd

theorem rpow_eq (a b : ℝ) : Real.rpow a b = a ^ b := rfl

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

end Provedd

open Provedd in
/-- `linear_neumann_centered_sampling_prefactor_absorbed_by_sample_lower`. -/
theorem solution
    (Cpref : ℝ) :
    0 < Cpref →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Centry : ℝ, 0 < Centry →
        let entryScale : ℝ :=
          Centry * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ))
        Cpref * entryScale *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                p) ≤
          (Cthreshold * Centry) * Real.rpow lam (-1) := by
  intro hCpref
  refine ⟨Cpref, hCpref, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hm hμ₀ hμ₁ p hsample Centry hCentry entryScale
  simp only [p, entryScale] -- unfold the lets
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN_def
  set Lg : ℝ := β * Real.log N with hLg_def
  have hn₁R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn₂
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0:ℝ) < μ₀ := by linarith
  have hμ₁0 : (0:ℝ) < μ₁ := by linarith
  have hlam0 : (0:ℝ) < lam := by linarith
  have hsqrtμ₀_pos : (0:ℝ) < Real.sqrt μ₀ := Real.sqrt_pos.mpr hμ₀0
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hsmall | hbig
  · -- N = 1: log N = 0 ⇒ Lg = 0 ⇒ the √(βN log N/p) factor = √0 = 0
    have hmaxeq : max n₁ n₂ = 1 := by have := le_max_left n₁ n₂; omega
    have hNval : N = 1 := by rw [hN_def, hmaxeq]; norm_num
    have hlog0 : Real.log N = 0 := by rw [hNval]; simp
    -- the outer √ factor: β*N*log N / p = 0
    rw [show (β * N * Real.log N) = 0 by rw [hlog0]; ring]
    simp only [zero_div, Real.sqrt_zero, mul_zero]
    have : (0:ℝ) ≤ Cpref * Centry * Real.rpow lam (-1) := by
      have : (0:ℝ) < Real.rpow lam (-1) := by rw [rpow_eq]; exact Real.rpow_pos_of_pos hlam0 _
      positivity
    linarith [this]
  · -- main
    have hn2le : (2:ℝ) ≤ N := by rw [hN_def]; exact_mod_cast hbig
    have hNpos : (0:ℝ) < N := by linarith
    have hlogpos : (0:ℝ) < Real.log N := Real.log_pos (by linarith)
    have hLg1 : (1:ℝ) ≤ Lg := by rw [hLg_def]; exact one_le_beta_log β N hβ hn2le hlogpos
    have hLgpos : (0:ℝ) < Lg := by linarith
    -- sample bound: m ≥ lam μ₁ max(√μ₀,μ₁) N r Lg
    have hsample' : (m:ℝ) ≥ lam * μ₁ * max (Real.sqrt μ₀) μ₁ * N * (r:ℝ) * Lg := by
      rw [hN_def, hLg_def, hN_def] at *; exact hsample
    have hmaxge : Real.sqrt μ₀ ≤ max (Real.sqrt μ₀) μ₁ := le_max_left _ _
    have hlbpos : (0:ℝ) < lam * μ₁ * max (Real.sqrt μ₀) μ₁ * N * (r:ℝ) * Lg := by
      have : (0:ℝ) < max (Real.sqrt μ₀) μ₁ := lt_of_lt_of_le hsqrtμ₀_pos hmaxge
      positivity
    have hmpos : (0:ℝ) < (m:ℝ) := lt_of_lt_of_le hlbpos hsample'
    -- m ≥ lam μ₁ √μ₀ N r Lg  (drop max to √μ₀)
    have hsample'' : (m:ℝ) ≥ lam * μ₁ * Real.sqrt μ₀ * N * (r:ℝ) * Lg := by
      have hstep : lam * μ₁ * Real.sqrt μ₀ * N * (r:ℝ) * Lg
          ≤ lam * μ₁ * max (Real.sqrt μ₀) μ₁ * N * (r:ℝ) * Lg := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hLgpos)
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hrR)
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hNpos)
        apply mul_le_mul_of_nonneg_left hmaxge (by positivity)
      linarith [hsample', hstep]
    -- merge the three square roots:
    -- √(r/(n₁n₂)) · √(μ₀ N r Lg/m) · √(N Lg n₁n₂/m) = √μ₀ · N · r · Lg / m
    -- (the outer factor √(βN log N/p) = √(N Lg · n₁n₂/m))
    have houter : (β * N * Real.log N) / ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
        = N * Lg * ((n₁:ℝ)*(n₂:ℝ)) / m := by
      rw [hLg_def]; field_simp
    rw [houter]
    -- now the product of three sqrts
    set A : ℝ := (r:ℝ)/((n₁:ℝ)*(n₂:ℝ)) with hA_def
    set Bb : ℝ := (μ₀ * N * (r:ℝ) * Lg) / m with hBb_def
    set Cc : ℝ := N * Lg * ((n₁:ℝ)*(n₂:ℝ)) / m with hCc_def
    have hAnn : (0:ℝ) ≤ A := by rw [hA_def]; positivity
    have hBbnn : (0:ℝ) ≤ Bb := by rw [hBb_def]; positivity
    have hsqrtprod : Real.sqrt A * Real.sqrt Bb * Real.sqrt Cc
        = Real.sqrt μ₀ * N * (r:ℝ) * Lg / m := by
      rw [← Real.sqrt_mul hAnn, ← Real.sqrt_mul (by positivity)]
      rw [show A * Bb * Cc = (μ₀ * N^2 * (r:ℝ)^2 * Lg^2) / m^2 by
        rw [hA_def, hBb_def, hCc_def]; field_simp]
      rw [show (μ₀ * N^2 * (r:ℝ)^2 * Lg^2) / m^2
          = μ₀ * (N * (r:ℝ) * Lg / m)^2 by field_simp]
      rw [Real.sqrt_mul (le_of_lt hμ₀0), Real.sqrt_sq (by positivity)]
      ring
    -- LHS = Cpref * (Centry * μ₁ * √A * √Bb) * √Cc = Cpref Centry μ₁ * (√A √Bb √Cc)
    have hLHS_eq :
        Cpref * (Centry * μ₁ * Real.sqrt A * Real.sqrt Bb) * Real.sqrt Cc
          = Cpref * Centry * μ₁ * (Real.sqrt μ₀ * N * (r:ℝ) * Lg / m) := by
      rw [show Cpref * (Centry * μ₁ * Real.sqrt A * Real.sqrt Bb) * Real.sqrt Cc
          = Cpref * Centry * μ₁ * (Real.sqrt A * Real.sqrt Bb * Real.sqrt Cc) by ring, hsqrtprod]
    rw [hLHS_eq]
    -- Cpref Centry μ₁ √μ₀ N r Lg/m ≤ Cpref Centry lam^(-1)
    -- using m ≥ lam μ₁ √μ₀ N r Lg
    rw [show Real.rpow lam (-1) = lam⁻¹ from Real.rpow_neg_one lam]
    -- goal: Cpref*Centry*μ₁*(√μ₀ N r Lg / m) ≤ (Cpref*Centry)*lam⁻¹
    have hCC : (0:ℝ) ≤ Cpref * Centry := by positivity
    rw [show Cpref * Centry * μ₁ * (Real.sqrt μ₀ * N * (r:ℝ) * Lg / m)
        = (Cpref * Centry) * ((μ₁ * Real.sqrt μ₀ * N * (r:ℝ) * Lg) / m) by ring]
    apply mul_le_mul_of_nonneg_left _ hCC
    -- (μ₁ √μ₀ N r Lg)/m ≤ lam⁻¹
    rw [div_le_iff₀ hmpos]
    -- μ₁ √μ₀ N r Lg ≤ lam⁻¹ * m
    have hgoal : μ₁ * Real.sqrt μ₀ * N * (r:ℝ) * Lg ≤ lam⁻¹ * m := by
      rw [inv_mul_eq_div, le_div_iff₀ hlam0]
      -- lam * (μ₁ √μ₀ N r Lg) ≤ m
      nlinarith [hsample'', hLgpos, hrR, hNpos, hμ₁0, hsqrtμ₀_pos, hlam0]
    linarith [hgoal]
