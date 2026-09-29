-- Prove2me | Definitions.Def_Tropical_Barrier4AdaptiveSaturation
-- name    : Tropical_Barrier4AdaptiveSaturation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:22.941587+00:00
-- url     : https://prove2.me/theorems/e80629e3-fdf3-4404-84cd-81ee09abf98c
-- title:
--   Aether Catalog definitions — Tropical_Barrier4AdaptiveSaturation
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Barrier4AdaptiveSaturation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Barrier4AdaptiveSaturation.lean by skeleton subtraction
import Mathlib

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

namespace Barrier4

open Real

/-! ## 1. The cost curve and the halving DP -/

/-- Expected total cost after committing to `k` binary queries on a window of width `W`:
`k` queries already paid plus the average residual scan `W / 2^(k+1)`. -/
noncomputable def netCost (W : ℝ) (k : ℕ) : ℝ := W / 2 ^ (k + 1) + k

/-- The halving DP: `V(1) = 1/2`, `V(2W) = V(W) + 1`, indexed by the dyadic exponent. -/
noncomputable def dpVal : ℕ → ℝ
  | 0 => 1 / 2
  | m + 1 => dpVal m + 1





/-! ## 1b. The curve is *generated* by iterated halving -/

/-- The genuine adaptive process: with no queries left the residual window of width `W` is
scanned at average cost `W/2`; each query costs `1` and halves the window. -/
noncomputable def halvingCost : ℝ → ℕ → ℝ
  | W, 0 => W / 2
  | W, (k + 1) => 1 + halvingCost (W / 2) k



/-! ## 2. The marginal-value identity -/



/-! ## 3. The pin is not the argmin -/






/-! ## 4. The general-`W` bracket -/








end Barrier4


