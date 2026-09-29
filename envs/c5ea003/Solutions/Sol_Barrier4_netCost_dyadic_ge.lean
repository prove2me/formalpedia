-- Prove2me | solution 1 for Barrier4.netCost_dyadic_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:41:25.844464+00:00
-- url     : https://prove2.me/submissions/0e3149e3-7fa7-49bc-b0b5-6af8bb6b5d15

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









open Barrier4 in
theorem solution(m k : ℕ) : (m : ℝ) ≤ netCost ((2:ℝ) ^ m) k := by
  rcases le_or_gt m k with h | h
  · have hpos : 0 < (2:ℝ) ^ m / 2 ^ (k + 1) := by positivity
    have : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    simp only [netCost]; linarith
  · -- `k ≤ m - 1`; write `m = k + 1 + d`
    obtain ⟨d, rfl⟩ : ∃ d, m = k + 1 + d := ⟨m - k - 1, by omega⟩
    have hpow : (2:ℝ) ^ (k + 1 + d) / 2 ^ (k + 1) = 2 ^ d := by
      rw [pow_add]
      field_simp
    have hd : (d : ℝ) + 1 ≤ 2 ^ d := by
      have : d + 1 ≤ 2 ^ d := Nat.lt_two_pow_self
      exact_mod_cast this
    simp only [netCost, hpow]
    push_cast
    linarith
