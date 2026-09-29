-- Prove2me | solution 1 for Barrier4.exists_dyadic_scale
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:41:25.329944+00:00
-- url     : https://prove2.me/submissions/b5e0b007-76ce-4d51-a528-f9355f4b9d1a

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
theorem solution{W : ℝ} (hW : 1 ≤ W) : ∃ k : ℕ, (2:ℝ) ^ k ≤ W ∧ W < 2 ^ (k + 1) := by
  classical
  have hex : ∃ n : ℕ, W < 2 ^ n := pow_unbounded_of_one_lt W (show (1:ℝ) < 2 by norm_num)
  have hn : W < 2 ^ (Nat.find hex) := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hn
    norm_num at hn
    linarith
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨k, ?_, by rw [← hk]; exact hn⟩
  have hmin := Nat.find_min hex (m := k) (by omega)
  push_neg at hmin
  exact hmin
