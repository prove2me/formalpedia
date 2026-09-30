-- Prove2me | solution 1 for mme_CW_multinomial_volume_frequent_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:17:46.537645+00:00
-- url     : https://prove2.me/submissions/7cf176cd-8398-4e61-a4d8-6de76937582b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecificLimits.Normed
open BigOperators Filter Topology

/-- The exponential lower bound `27^M ≤ 4^M (3M+1) C(3M, M)`, by induction on `M`. -/
private lemma choose_three_lower (M : ℕ) :
    (27 : ℝ) ^ M ≤ 4 ^ M * (3 * M + 1) * ((3 * M).choose M : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hc : ∀ N : ℕ, ((3 * N).choose N : ℝ) * N.factorial * (2 * N).factorial
        = (3 * N).factorial := by
      intro N
      have h := Nat.choose_mul_factorial_mul_factorial (show N ≤ 3 * N by omega)
      rw [show 3 * N - N = 2 * N by omega] at h
      exact_mod_cast h
    have hM := hc M
    have hM1 := hc (M + 1)
    set c0 : ℝ := ((3 * M).choose M : ℝ) with hc0def
    set c1 : ℝ := ((3 * (M + 1)).choose (M + 1) : ℝ) with hc1def
    have hf1 : ((M + 1).factorial : ℝ) = (M + 1) * M.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf2 : ((2 * (M + 1)).factorial : ℝ) = (2 * M + 2) * (2 * M + 1) * (2 * M).factorial := by
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hf3 : ((3 * (M + 1)).factorial : ℝ)
        = (3 * M + 3) * (3 * M + 2) * (3 * M + 1) * (3 * M).factorial := by
      rw [show 3 * (M + 1) = 3 * M + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast; ring
    rw [hf1, hf2, hf3] at hM1
    have hF : ((M.factorial : ℝ) * (2 * M).factorial) ≠ 0 := by positivity
    have key : c1 * (((M : ℝ) + 1) * (2 * M + 2) * (2 * M + 1))
        = (3 * M + 3) * (3 * M + 2) * (3 * M + 1) * c0 := by
      apply mul_right_cancel₀ hF
      linear_combination hM1 - ((3 * (M : ℝ) + 3) * (3 * M + 2) * (3 * M + 1)) * hM
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hX : 0 < ((M : ℝ) + 1) * (2 * M + 2) * (2 * M + 1) := by positivity
    have hc0 : 0 ≤ c0 := by positivity
    have hpoly : 27 * (3 * (M : ℝ) + 1) * (((M : ℝ) + 1) * (2 * M + 2) * (2 * M + 1))
        ≤ 4 * (3 * ((M : ℝ) + 1) + 1) * ((3 * M + 3) * (3 * M + 2) * (3 * M + 1)) := by
      nlinarith [mul_nonneg (mul_nonneg hM0 hM0) hM0, mul_nonneg hM0 hM0, hM0]
    have step : 27 * (3 * (M : ℝ) + 1) * c0 ≤ 4 * (3 * ((M : ℝ) + 1) + 1) * c1 := by
      apply le_of_mul_le_mul_right _ hX
      calc 27 * (3 * (M : ℝ) + 1) * c0 * (((M : ℝ) + 1) * (2 * M + 2) * (2 * M + 1))
          = c0 * (27 * (3 * (M : ℝ) + 1) * (((M : ℝ) + 1) * (2 * M + 2) * (2 * M + 1))) := by ring
        _ ≤ c0 * (4 * (3 * ((M : ℝ) + 1) + 1) * ((3 * M + 3) * (3 * M + 2) * (3 * M + 1))) :=
            mul_le_mul_of_nonneg_left hpoly hc0
        _ = 4 * (3 * ((M : ℝ) + 1) + 1) * (c1 * (((M : ℝ) + 1) * (2 * M + 2) * (2 * M + 1))) := by
            rw [key]; ring
        _ = 4 * (3 * ((M : ℝ) + 1) + 1) * c1 * (((M : ℝ) + 1) * (2 * M + 2) * (2 * M + 1)) := by
            ring
    push_cast
    calc (27 : ℝ) ^ (M + 1) = 27 * 27 ^ M := by ring
      _ ≤ 27 * (4 ^ M * (3 * M + 1) * c0) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 4 ^ M * (27 * (3 * (M : ℝ) + 1) * c0) := by ring
      _ ≤ 4 ^ M * (4 * (3 * ((M : ℝ) + 1) + 1) * c1) :=
          mul_le_mul_of_nonneg_left step (by positivity)
      _ = 4 ^ (M + 1) * (3 * ((M : ℝ) + 1) + 1) * c1 := by ring

theorem solution
    (q : ℕ) (_hq : 1 ≤ q)
    (V : ℝ) (_hV_nn : 0 ≤ V) (_hV_cubed : V^3 < 3 * (q : ℝ))
    (ε : ℝ) (_hε : 0 < ε) :
    ∃ᶠ (M : ℕ) in atTop,
      V ^ (3 * M) * (1 - ε) ≤
        ((Nat.factorial (3 * M) /
          (Nat.factorial M * Nat.factorial M * Nat.factorial M) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) *
        ((q : ℝ)) ^ M := by
  apply Filter.Eventually.frequently
  -- The integer `(3M)! / (M!)^3` is the product of two binomial coefficients.
  have hT : ∀ M : ℕ, Nat.factorial (3 * M) / (Nat.factorial M * Nat.factorial M * Nat.factorial M)
      = (3 * M).choose M * (2 * M).choose M := by
    intro M
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    have h1 := Nat.choose_mul_factorial_mul_factorial (show M ≤ 3 * M by omega)
    have h2 := Nat.choose_mul_factorial_mul_factorial (show M ≤ 2 * M by omega)
    rw [show 3 * M - M = 2 * M by omega] at h1
    rw [show 2 * M - M = M by omega] at h2
    rw [← h1, ← h2]; ring
  -- Exponential lower bound `27^M ≤ (3M+1)(2M+1) T_M`.
  have hTlow : ∀ M : ℕ, (27 : ℝ) ^ M ≤ (3 * M + 1) * (2 * M + 1) *
      ((Nat.factorial (3 * M) / (Nat.factorial M * Nat.factorial M * Nat.factorial M) : ℕ) : ℝ) := by
    intro M
    rw [hT M]
    push_cast
    have h1 := choose_three_lower M
    have h2 : (4 : ℝ) ^ M ≤ (2 * M + 1) * ((2 * M).choose M : ℝ) := by
      exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_central_binom M
    calc (27 : ℝ) ^ M ≤ 4 ^ M * (3 * M + 1) * ((3 * M).choose M : ℝ) := h1
      _ ≤ ((2 * M + 1) * ((2 * M).choose M : ℝ)) * (3 * M + 1) * ((3 * M).choose M : ℝ) := by
          gcongr
      _ = _ := by ring
  -- The geometric ratio.
  have hq0 : (0 : ℝ) < q := by exact_mod_cast _hq
  set a : ℝ := V ^ 9 with ha_def
  set b : ℝ := 27 * (q : ℝ) ^ 3 with hb_def
  have ha : 0 ≤ a := by positivity
  have hb : 0 < b := by positivity
  have hab : a < b := by
    have h := pow_lt_pow_left₀ _hV_cubed (by positivity) (show (3 : ℕ) ≠ 0 by norm_num)
    calc a = (V ^ 3) ^ 3 := by rw [ha_def]; ring
      _ < (3 * (q : ℝ)) ^ 3 := h
      _ = b := by rw [hb_def]; ring
  set r : ℝ := a / b with hr_def
  have hr0 : 0 ≤ r := div_nonneg ha hb.le
  have hr1 : r < 1 := (div_lt_one hb).mpr hab
  have hrabs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have ht2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hrabs
  have ht1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hrabs
  have ht0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 hrabs
  have hg : Tendsto (fun M : ℕ => (1 - ε) ^ 3 * ((3 * (M : ℝ) + 1) * (2 * M + 1)) * r ^ M)
      atTop (𝓝 0) := by
    have h := ((ht2.const_mul 6).add (ht1.const_mul 5)).add ht0
    simp only [mul_zero, add_zero] at h
    have h' := h.const_mul ((1 - ε) ^ 3)
    rw [mul_zero] at h'
    refine h'.congr (fun M => ?_)
    simp only [pow_one, pow_zero, one_mul]
    ring
  have hev : ∀ᶠ M : ℕ in atTop,
      (1 - ε) ^ 3 * ((3 * (M : ℝ) + 1) * (2 * M + 1)) * r ^ M < 1 := by
    have := hg.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact this
  filter_upwards [hev] with M hM
  set T : ℝ := ((Nat.factorial (3 * M) /
      (Nat.factorial M * Nat.factorial M * Nat.factorial M) : ℕ) : ℝ) with hT_def
  have hT0 : 0 ≤ T := by positivity
  have hRHS : 0 ≤ T ^ ((1 : ℝ) / 3) * (q : ℝ) ^ M := by positivity
  rcases le_or_gt (1 - ε) 0 with hε1 | hε1
  · -- `1 - ε ≤ 0`: the left side is nonpositive.
    have : V ^ (3 * M) * (1 - ε) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hε1
    linarith
  · have hLHS : 0 ≤ V ^ (3 * M) * (1 - ε) := by positivity
    -- Compare cubes.
    rw [← pow_le_pow_iff_left₀ hLHS hRHS (show (3 : ℕ) ≠ 0 by norm_num)]
    have hcube : (T ^ ((1 : ℝ) / 3)) ^ 3 = T := by
      rw [show ((1 : ℝ) / 3) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hT0 (by norm_num)
    have hP : 0 < (3 * (M : ℝ) + 1) * (2 * M + 1) := by positivity
    have hbM : 0 < b ^ M := pow_pos hb M
    -- From `g(M) < 1`: `(1-ε)^3 (3M+1)(2M+1) a^M < b^M`.
    have hrM : r ^ M = a ^ M / b ^ M := by rw [hr_def, div_pow]
    have h1 : (1 - ε) ^ 3 * ((3 * (M : ℝ) + 1) * (2 * M + 1)) * a ^ M < b ^ M := by
      rw [hrM] at hM
      have := mul_lt_mul_of_pos_right hM hbM
      rw [one_mul] at this
      calc (1 - ε) ^ 3 * ((3 * (M : ℝ) + 1) * (2 * M + 1)) * a ^ M
          = (1 - ε) ^ 3 * ((3 * (M : ℝ) + 1) * (2 * M + 1)) * (a ^ M / b ^ M) * b ^ M := by
            field_simp
        _ < b ^ M := this
    -- And `b^M = 27^M q^(3M) ≤ (3M+1)(2M+1) T q^(3M)`.
    have h2 : b ^ M ≤ (3 * (M : ℝ) + 1) * (2 * M + 1) * T * ((q : ℝ) ^ 3) ^ M := by
      have := hTlow M
      rw [← hT_def] at this
      calc b ^ M = 27 ^ M * ((q : ℝ) ^ 3) ^ M := by rw [hb_def, mul_pow]
        _ ≤ ((3 * (M : ℝ) + 1) * (2 * M + 1) * T) * ((q : ℝ) ^ 3) ^ M :=
            mul_le_mul_of_nonneg_right this (by positivity)
    have h3 : (1 - ε) ^ 3 * a ^ M ≤ T * ((q : ℝ) ^ 3) ^ M := by
      have h12 := lt_of_lt_of_le h1 h2
      have : (3 * (M : ℝ) + 1) * (2 * M + 1) * ((1 - ε) ^ 3 * a ^ M)
          ≤ (3 * (M : ℝ) + 1) * (2 * M + 1) * (T * ((q : ℝ) ^ 3) ^ M) := by
        calc (3 * (M : ℝ) + 1) * (2 * M + 1) * ((1 - ε) ^ 3 * a ^ M)
            = (1 - ε) ^ 3 * ((3 * (M : ℝ) + 1) * (2 * M + 1)) * a ^ M := by ring
          _ ≤ (3 * (M : ℝ) + 1) * (2 * M + 1) * T * ((q : ℝ) ^ 3) ^ M := h12.le
          _ = (3 * (M : ℝ) + 1) * (2 * M + 1) * (T * ((q : ℝ) ^ 3) ^ M) := by ring
      exact le_of_mul_le_mul_left this hP
    calc (V ^ (3 * M) * (1 - ε)) ^ 3 = (1 - ε) ^ 3 * a ^ M := by rw [ha_def]; ring
      _ ≤ T * ((q : ℝ) ^ 3) ^ M := h3
      _ = (T ^ ((1 : ℝ) / 3) * (q : ℝ) ^ M) ^ 3 := by rw [mul_pow, hcube]; ring
