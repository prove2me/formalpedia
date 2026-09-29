-- Prove2me | solution 1 for Barrier4.netCost_le_logb_add_half
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:41:26.392752+00:00
-- url     : https://prove2.me/submissions/fad0cdaf-8955-4f04-8bda-a460d77af69a

-- Sol generated from Tropical/Barrier4AdaptiveSaturation.lean
import Mathlib
import Definitions.Def_Tropical_Barrier4AdaptiveSaturation

/-!
# Barrier-4 positional converse, stratum T2: adaptive saturation `V(W) = log₂ W + ½`

The T2 stratum studies the *adaptive* (query-then-scan) cost curve on a window of width `W`:
after `k` binary queries the surviving window has width `W / 2^k`, and a residual linear scan of
a window of width `w` costs `w / 2` on average.  This gives the **cost curve**

`netCost W k = W / 2^(k+1) + k`   (residual scan + queries already paid).

Four things are proved.

* `marginal_net_identity` : the *net* marginal-value identity
  `cost(k) − cost(k+1) = W / 2^(k+2) − 1`, exactly (the *gross* form, without the `−1` query
  charge, is false — see `gross_marginal_identity_fails`).
* `saturation_exact` / `dpVal_eq` : on dyadic windows `W = 2^m` the **pinned** value saturates
  exactly: `netCost (2^m) m = m + 1/2 = log₂ W + 1/2`, and this is precisely the fixed point of
  the halving recursion `V(2W) = V(W) + 1`, `V(1) = 1/2`.
* `netCost_dyadic_ge` together with `netCost_pin_sub_one` and `netCost_pin_sub_two` : the pin is
  **not** the argmin.  On `W = 2^m` the minimum of the cost curve equals `m` and is attained at
  the two offsets `k = m − 1` and `k = m − 2`; the pinned value `m + 1/2` sits a half query above
  it (`pin_not_argmin`).  Three distinct `k`'s (the pin `log₂ W`, the argmin `log₂ W − 1`, and the
  economic optimum one query further out) must therefore be kept apart.
* `netCost_bracket` : for a general window `W ≥ 1` the closed form `log₂ W + 1/2` is an upper
  bound for the optimised curve which is **never undercut by more than `1/2`**:
  `log₂ W − 1/2 ≤ min_k netCost W k ≤ log₂ W + 1/2`, the upper bound being attained exactly on
  dyadic `W`.
-/

open Barrier4

open Real

/-! ## 1. The cost curve and the halving DP -/







/-! ## 1b. The curve is *generated* by iterated halving -/




/-! ## 2. The marginal-value identity -/



/-! ## 3. The pin is not the argmin -/






/-! ## 4. The general-`W` bracket -/

private lemma logb_two_eq (x : ℝ) : Real.logb 2 x = Real.log x / Real.log 2 := rfl

private lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)







open Barrier4 in
theorem solution{W : ℝ} {k : ℕ} (h1 : (2:ℝ) ^ k ≤ W) (h2 : W < 2 ^ (k + 1)) :
    netCost W k ≤ Real.logb 2 W + 1 / 2 := by
  have hpos : (0:ℝ) < 2 ^ k := by positivity
  have hW : 0 < W := lt_of_lt_of_le hpos h1
  set t : ℝ := W / 2 ^ k with ht_def
  have ht1 : 1 ≤ t := by rw [ht_def, le_div_iff₀ hpos]; linarith
  have ht2 : t < 2 := by
    rw [ht_def, div_lt_iff₀ hpos]
    calc W < 2 ^ (k + 1) := h2
      _ = 2 * 2 ^ k := by ring
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hsplit : Real.logb 2 W = Real.logb 2 t + k := by
    have hWt : W = t * 2 ^ k := by rw [ht_def]; field_simp
    rw [hWt, Real.logb_mul (ne_of_gt ht0) (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num)]
    ring
  -- `log t ≥ 1 - 1/t` and `t < 2 < 2 / log 2` give `t/2 - 1/2 ≤ log₂ t`
  have hlog : 1 - 1 / t ≤ Real.log t := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / t by positivity)
    rw [Real.log_div one_ne_zero (ne_of_gt ht0), Real.log_one] at h
    have : Real.log t ≥ 1 - 1 / t := by linarith
    linarith
  have hl2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hkey : (t / 2 - 1 / 2) * Real.log 2 ≤ Real.log t := by
    have h1t : (t - 1) / t ≤ Real.log t := by
      have : 1 - 1 / t = (t - 1) / t := by field_simp
      linarith [this ▸ hlog]
    have hstep : (t / 2 - 1 / 2) * Real.log 2 ≤ (t - 1) / t := by
      rw [le_div_iff₀ ht0]
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 ht2.le)]
    linarith
  have hlogb : t / 2 - 1 / 2 ≤ Real.logb 2 t := by
    rw [logb_two_eq, le_div_iff₀ log_two_pos]
    exact hkey
  have hcost : netCost W k = t / 2 + k := by
    simp only [netCost, ht_def]
    rw [pow_succ]
    field_simp
  rw [hcost, hsplit]
  linarith
