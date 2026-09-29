-- Prove2me | Theorems.Thm_Barrier4_exists_dyadic_scale
-- name    : Barrier4.exists_dyadic_scale
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:33:50.940511+00:00
-- url     : https://prove2.me/theorems/0d128849-9236-47dc-90c8-0d356f15b198
-- title:
--   Every window of width at least `1` sits in a unique dyadic scale.
-- statement:
--   Every window of width at least `1` sits in a unique dyadic scale.
--
--   ```lean
--   theorem Barrier4.exists_dyadic_scale{W : ℝ} (hW : 1 ≤ W) : ∃ k : ℕ, (2:ℝ) ^ k ≤ W ∧ W < 2 ^ (k + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/Barrier4AdaptiveSaturation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/Barrier4AdaptiveSaturation.lean#L254

-- Thm stub generated from Tropical/Barrier4AdaptiveSaturation.lean
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

theorem Barrier4.exists_dyadic_scale{W : ℝ} (hW : 1 ≤ W) : ∃ k : ℕ, (2:ℝ) ^ k ≤ W ∧ W < 2 ^ (k + 1) := by sorry
