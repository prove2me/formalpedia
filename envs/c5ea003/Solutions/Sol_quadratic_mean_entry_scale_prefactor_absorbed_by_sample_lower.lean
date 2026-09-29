-- Prove2me | solution 1 for quadratic_mean_entry_scale_prefactor_absorbed_by_sample_lower
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-22T03:24:51.064753+00:00
-- url     : https://prove2.me/submissions/1cb6c209-a8c1-4471-a706-2a948533d819

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
open scoped Classical BigOperators

namespace MatrixCompletion

end MatrixCompletion

open MatrixCompletion

set_option maxHeartbeats 1600000 in
theorem solution
    (Cpref Centry : ℝ) :
    0 < Cpref → 0 < Centry →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        Cpref * Centry *
            |1 - ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))| *
            μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCpref hCentry
  refine ⟨Cpref * Centry, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hmlb
  -- abbreviations
  set N : ℝ := (n₁ : ℝ) * (n₂ : ℝ) with hN
  set M : ℝ := (↑(max n₁ n₂) : ℝ) with hMdef
  set p : ℝ := (m : ℝ) / N with hp
  -- basic positivity facts
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hNpos : 0 < N := by rw [hN]; positivity
  have hlampos : 0 < lam := lt_of_lt_of_le one_pos hlam
  have hμ₀pos : 0 < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hβpos : 0 < β := by linarith
  -- M ≥ 1 since max ≥ 1
  have hmaxpos : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left _ _)
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hmaxpos
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  -- N ≤ M^2
  have hNM : N ≤ M ^ 2 := by
    rw [hN, hMdef, sq]
    have h1 : (n₁ : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast Nat.le_max_left n₁ n₂
    have h2 : (n₂ : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast Nat.le_max_right n₁ n₂
    exact mul_le_mul h1 h2 (le_of_lt hn₂R) (by exact_mod_cast Nat.zero_le _)
  -- RHS is positive
  have htpos : 0 < Real.rpow lam (-((3 : ℝ) / 2)) := Real.rpow_pos_of_pos hlampos _
  have hRHSnn : 0 ≤ Cpref * Centry * Real.rpow lam (-((3 : ℝ) / 2)) := by positivity
  -- Corner case 1: m = 0  ⇒  p = 0  ⇒  p⁻¹ = 0  ⇒  LHS = 0
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- p = 0
    have hp0 : p = 0 := by rw [hp, hm0]; simp
    have : Cpref * Centry * |1 - p| * μ₀ ^ 2 * ((r : ℝ) / M) ^ 2 * p⁻¹ *
        Real.sqrt ((β * M * Real.log M) / p) = 0 := by
      rw [hp0]; simp
    rw [this]
    exact hRHSnn
  -- Corner case 2: max n₁ n₂ = 1  ⇒  M = 1  ⇒  log M = 0  ⇒  sqrt arg numerator = 0
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hmax1 | hmax2
  · -- max < 2 and ≥ 1 ⇒ max = 1 ⇒ M = 1 ⇒ log M = 0
    have hmaxeq : max n₁ n₂ = 1 := by omega
    have hMeq : M = 1 := by rw [hMdef, hmaxeq]; norm_num
    have hlog0 : Real.log M = 0 := by rw [hMeq]; exact Real.log_one
    have : Cpref * Centry * |1 - p| * μ₀ ^ 2 * ((r : ℝ) / M) ^ 2 * p⁻¹ *
        Real.sqrt ((β * M * Real.log M) / p) = 0 := by
      rw [hlog0]; simp
    rw [this]
    exact hRHSnn
  -- MAIN CASE: m ≥ 1, max ≥ 2
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hppos : 0 < p := by rw [hp]; positivity
  have hM2 : (2 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast hmax2
  -- log M ≥ log 2 > 1/2
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlogM_ge : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM2
  have hlogMpos : 0 < Real.log M := lt_of_lt_of_le (by linarith) hlogM_ge
  -- KEY ABSORPTION FACT: β * log M ≥ 1
  have hkey : (1 : ℝ) ≤ β * Real.log M := by
    have h2logM : (1 : ℝ) < 2 * Real.log M := by linarith
    nlinarith [hlogMpos, hβpos]
  -- cube identities for the rpow factors in L
  have hcubeμ : (Real.rpow μ₀ ((4 : ℝ) / 3)) ^ 3 = μ₀ ^ 4 := by
    have key : (μ₀ ^ ((4:ℝ)/3)) ^ ((3:ℕ):ℝ) = μ₀ ^ 4 := by
      rw [← Real.rpow_mul (le_of_lt hμ₀pos), ← Real.rpow_natCast μ₀ 4]
      congr 1; norm_num
    rw [Real.rpow_natCast (μ₀ ^ ((4:ℝ)/3)) 3] at key
    exact key
  have hcuber : (Real.rpow (r : ℝ) ((4 : ℝ) / 3)) ^ 3 = (r : ℝ) ^ 4 := by
    have key : ((r:ℝ) ^ ((4:ℝ)/3)) ^ ((3:ℕ):ℝ) = (r:ℝ) ^ 4 := by
      rw [← Real.rpow_mul (le_of_lt hrR), ← Real.rpow_natCast (r:ℝ) 4]
      congr 1; norm_num
    rw [Real.rpow_natCast ((r:ℝ) ^ ((4:ℝ)/3)) 3] at key
    exact key
  -- p ≤ 1
  have hple1 : p ≤ 1 := by
    rw [hp, div_le_one hNpos]
    rw [hN]; exact_mod_cast hm
  -- |1 - p| ≤ 1
  have habs1 : |1 - p| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  -- set abbreviations for the factored form
  set c : ℝ := Cpref * Centry with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set t : ℝ := Real.rpow lam (-((3:ℝ)/2)) with ht
  -- the "A" factor
  set A : ℝ := |1 - p| * μ₀ ^ 2 * ((r : ℝ) / M) ^ 2 * p⁻¹ *
      Real.sqrt ((β * M * Real.log M) / p) with hA
  -- A ≥ 0
  have hsqrt_nn : 0 ≤ Real.sqrt ((β * M * Real.log M) / p) := Real.sqrt_nonneg _
  have hAnn : 0 ≤ A := by
    rw [hA]; positivity
  have htnn : 0 ≤ t := le_of_lt htpos
  -- t^2 = lam^(-3)
  have ht2 : t ^ 2 = Real.rpow lam (-(3:ℝ)) := by
    rw [ht]
    have key : (lam ^ (-((3:ℝ)/2))) ^ ((2:ℕ):ℝ) = Real.rpow lam (-(3:ℝ)) := by
      rw [← Real.rpow_mul (le_of_lt hlampos)]
      congr 1; norm_num
    rw [Real.rpow_natCast (lam ^ (-((3:ℝ)/2))) 2] at key
    exact key
  -- KEY: A ≤ t. Prove via A^2 ≤ t^2.
  have hAle : A ≤ t := by
    -- sqrt argument is nonneg
    have hsarg_nn : 0 ≤ (β * M * Real.log M) / p := by positivity
    have hsq_sqrt : (Real.sqrt ((β * M * Real.log M) / p)) ^ 2 = (β * M * Real.log M) / p :=
      Real.sq_sqrt hsarg_nn
    -- expand A^2
    have hA2_eq : A ^ 2 = |1 - p| ^ 2 * μ₀ ^ 4 * ((r : ℝ) / M) ^ 4 * (p⁻¹) ^ 2 *
        ((β * M * Real.log M) / p) := by
      rw [hA]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, hsq_sqrt]
      ring
    -- L and its cube
    set L : ℝ := lam * Real.rpow μ₀ ((4:ℝ)/3) * M * Real.rpow (r:ℝ) ((4:ℝ)/3) *
        (β * Real.log M) with hLdef
    have hLnn : 0 ≤ L := by
      rw [hLdef]
      have h1 : 0 ≤ Real.rpow μ₀ ((4:ℝ)/3) := Real.rpow_nonneg (le_of_lt hμ₀pos) _
      have h2 : 0 ≤ Real.rpow (r:ℝ) ((4:ℝ)/3) := Real.rpow_nonneg (le_of_lt hrR) _
      positivity
    have hmL : L ≤ (m : ℝ) := by rw [hLdef]; exact hmlb
    have hm3 : L ^ 3 ≤ (m : ℝ) ^ 3 := by
      exact pow_le_pow_left₀ hLnn hmL 3
    -- L^3 expansion using cube identities
    have hL3_eq : L ^ 3 = lam ^ 3 * μ₀ ^ 4 * M ^ 3 * (r : ℝ) ^ 4 * (β * Real.log M) ^ 3 := by
      rw [hLdef]
      have : (lam * Real.rpow μ₀ ((4:ℝ)/3) * M * Real.rpow (r:ℝ) ((4:ℝ)/3) *
          (β * Real.log M)) ^ 3
          = lam ^ 3 * (Real.rpow μ₀ ((4:ℝ)/3)) ^ 3 * M ^ 3 *
            (Real.rpow (r:ℝ) ((4:ℝ)/3)) ^ 3 * (β * Real.log M) ^ 3 := by ring
      rw [this, hcubeμ, hcuber]
    -- p⁻¹ = N / m
    have hpinv : p⁻¹ = N / (m : ℝ) := by
      rw [hp]; rw [inv_div]
    -- t^2 = (lam^3)⁻¹
    have ht2inv : t ^ 2 = (lam ^ 3)⁻¹ := by
      rw [ht2]
      show lam ^ (-(3:ℝ)) = (lam ^ 3)⁻¹
      rw [Real.rpow_neg (le_of_lt hlampos)]
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    -- helper facts
    have hlogMnn : 0 ≤ Real.log M := le_of_lt hlogMpos
    have hN3M6 : N ^ 3 ≤ M ^ 6 := by
      have : N ^ 3 ≤ (M ^ 2) ^ 3 := pow_le_pow_left₀ (le_of_lt hNpos) hNM 3
      calc N ^ 3 ≤ (M ^ 2) ^ 3 := this
        _ = M ^ 6 := by ring
    have hbetalog_sq : (1 : ℝ) ≤ (β * Real.log M) ^ 2 := by
      calc (1:ℝ) = 1 ^ 2 := by norm_num
        _ ≤ (β * Real.log M) ^ 2 := by
            apply pow_le_pow_left₀ (by norm_num) hkey
    have hL3pos : 0 < L ^ 3 := by
      rw [hL3_eq]; positivity
    have hm3pos : 0 < (m : ℝ) ^ 3 := by positivity
    have hA2le : A ^ 2 ≤ t ^ 2 := by
      rw [hA2_eq, ht2inv]
      -- rewrite |1-p|^2 ≤ 1 and p⁻¹, p in terms of N, m
      have habs1sq : |1 - p| ^ 2 ≤ 1 := by
        calc |1 - p| ^ 2 ≤ 1 ^ 2 := by
              apply pow_le_pow_left₀ (abs_nonneg _) habs1
          _ = 1 := by norm_num
      -- bound the |1-p|^2 factor by 1
      have hrest_nn : 0 ≤ μ₀ ^ 4 * ((r : ℝ) / M) ^ 4 * (p⁻¹) ^ 2 *
          ((β * M * Real.log M) / p) := by positivity
      calc |1 - p| ^ 2 * μ₀ ^ 4 * ((r : ℝ) / M) ^ 4 * (p⁻¹) ^ 2 *
              ((β * M * Real.log M) / p)
          = |1 - p| ^ 2 * (μ₀ ^ 4 * ((r : ℝ) / M) ^ 4 * (p⁻¹) ^ 2 *
              ((β * M * Real.log M) / p)) := by ring
        _ ≤ 1 * (μ₀ ^ 4 * ((r : ℝ) / M) ^ 4 * (p⁻¹) ^ 2 *
              ((β * M * Real.log M) / p)) := by
              exact mul_le_mul_of_nonneg_right habs1sq hrest_nn
        _ = μ₀ ^ 4 * ((r : ℝ) / M) ^ 4 * (p⁻¹) ^ 2 * ((β * M * Real.log M) / p) := by ring
        _ = μ₀ ^ 4 * (r : ℝ) ^ 4 * (β * M * Real.log M) * N ^ 3 / (M ^ 4 * (m : ℝ) ^ 3) := by
              rw [hpinv]
              rw [hp]
              field_simp
        _ ≤ (lam ^ 3)⁻¹ := by
              have hlam3pos : 0 < lam ^ 3 := by positivity
              -- Step A: replace N^3 by M^6 (numerator monotone up; denom fixed)
              calc μ₀ ^ 4 * (r : ℝ) ^ 4 * (β * M * Real.log M) * N ^ 3 /
                      (M ^ 4 * (m : ℝ) ^ 3)
                  ≤ μ₀ ^ 4 * (r : ℝ) ^ 4 * (β * M * Real.log M) * M ^ 6 /
                      (M ^ 4 * (m : ℝ) ^ 3) := by
                    gcongr
                _ = μ₀ ^ 4 * (r : ℝ) ^ 4 * (β * Real.log M) * M ^ 3 / (m : ℝ) ^ 3 := by
                    rw [div_eq_div_iff (by positivity) (by positivity)]
                    ring
                -- Step B: replace m^3 (denom) by L^3 (smaller ⇒ fraction larger)
                _ ≤ μ₀ ^ 4 * (r : ℝ) ^ 4 * (β * Real.log M) * M ^ 3 / L ^ 3 := by
                    gcongr
                -- Step C: expand L^3 and cancel ⇒ 1/(lam^3 * (β log M)^2)
                _ = 1 / (lam ^ 3 * (β * Real.log M) ^ 2) := by
                    rw [hL3_eq]
                    rw [div_eq_div_iff (by positivity) (by positivity)]
                    ring
                -- Step D: (β log M)^2 ≥ 1 ⇒ ≤ 1/lam^3 = (lam^3)⁻¹
                _ ≤ 1 / lam ^ 3 := by
                    apply div_le_div_of_nonneg_left (by norm_num) hlam3pos
                    calc lam ^ 3 = lam ^ 3 * 1 := by ring
                      _ ≤ lam ^ 3 * (β * Real.log M) ^ 2 := by
                          apply mul_le_mul_of_nonneg_left hbetalog_sq (le_of_lt hlam3pos)
                _ = (lam ^ 3)⁻¹ := by rw [one_div]
    -- conclude A ≤ t from A^2 ≤ t^2, both nonneg, via sqrt monotonicity
    have := Real.sqrt_le_sqrt hA2le
    rwa [Real.sqrt_sq hAnn, Real.sqrt_sq htnn] at this
  -- conclude
  calc c * |1 - p| * μ₀ ^ 2 * ((r : ℝ) / M) ^ 2 * p⁻¹ *
          Real.sqrt ((β * M * Real.log M) / p)
      = c * A := by rw [hA]; ring
    _ ≤ c * t := by exact mul_le_mul_of_nonneg_left hAle (le_of_lt hcpos)
