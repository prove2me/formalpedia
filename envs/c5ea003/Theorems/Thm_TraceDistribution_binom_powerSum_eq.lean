-- Prove2me | Theorems.Thm_TraceDistribution_binom_powerSum_eq
-- name    : TraceDistribution.binom_powerSum_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:55:55.791627+00:00
-- url     : https://prove2.me/theorems/823c325d-14b0-4e0e-9bea-f3a2b3b6c0dd
-- title:
--   The two multisets have identical power sums up to degree `n - 1`.
-- statement:
--   **The two multisets have identical power sums up to degree `n - 1`.**
--
--   ```lean
--   theorem TraceDistribution.binom_powerSum_eq(n j : ℕ) (hj : j < n) :
--       (Multiset.map (fun a => a ^ j) (binomEven n)).sum
--         = (Multiset.map (fun a => a ^ j) (binomOdd n)).sum := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/TraceDistribution/Sharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/TraceDistribution/Sharpness.lean#L118

-- Thm stub generated from Logic/TraceDistribution/Sharpness.lean
import Mathlib
import Definitions.Def_Logic_TraceDistribution_Sharpness
/-
# The power-sum threshold is exactly optimal

`Logic.TraceDistribution.PowerSums` shows that a multiset of naturals with all values
`< n` (equivalently, with joint support of size `≤ n`) is determined by its power sums
`p_0, …, p_{n-1}`.  This file proves that this threshold cannot be lowered by even one
degree, by an explicit construction:

`binomEven n` and `binomOdd n` are the *even* and *odd* parts of the `n`-th alternating
binomial (finite-difference) measure on `{0, 1, …, n}`, i.e.

  `binomEven n = ⨄_{k ≤ n, n-k even} C(n,k) copies of k`,
  `binomOdd  n = ⨄_{k ≤ n, n-k odd } C(n,k) copies of k`.

Because the `n`-th forward difference annihilates every polynomial of degree `< n`, the
two multisets have *identical* power sums `p_0, …, p_{n-1}`, while they differ (the
value `n` occurs once in the first and never in the second).  Both have all values
`≤ n` and joint support exactly `{0, …, n}`, of size `n + 1`.

Combining with `multiset_eq_of_powerSum_eq` this pins the threshold exactly:

* `powerSum_rigidity_at_threshold` — `n + 1` power sums suffice;
* `powerSum_rigidity_fails_below_threshold` — `n` power sums do not.

This is the *cross-domain* half of the trace-distribution story: rigidity comes from
Lagrange interpolation (linear algebra over `ℚ`), and the exact failure boundary comes
from the calculus of finite differences (the binomial transform).

## Lab notes (experimental data)

`n = 2`: `binomEven 2 = {0, 2}` (`k = 0, 2`), `binomOdd 2 = {1, 1}`.
  `p_0 : 2 = 2`,  `p_1 : 2 = 2`,  `p_2 : 4 ≠ 2`.  Threshold `n + 1 = 3` is needed.
`n = 3`: `binomEven 3 = {1,1,1,3}`, `binomOdd 3 = {0,2,2,2}`.
  `p_0 : 4 = 4`,  `p_1 : 6 = 6`,  `p_2 : 12 = 12`,  `p_3 : 30 ≠ 24`.
`n = 4`: `binomEven 4 = {0,2,2,2,2,2,2,4}`, `binomOdd 4 = {1,1,1,1,3,3,3,3}`.
  `p_0 = 8 = 8`, `p_1 = 16 = 16`, `p_2 = 40 = 40`, `p_3 = 112 = 112`, `p_4 = 352 ≠ 328`.
`n = 5`: `p_0 … p_4` all agree (`16, 40, 120, 400, 1440`), and `p_5 : 5560 ≠ 5440`.

The top-degree gaps are `4-2 = 2`, `30-24 = 6`, `352-328 = 24`, `5560-5440 = 120`, i.e.
exactly `n !` (OEIS A000142).  This is proved in general as `binom_powerSum_top_gap`,
so the two multisets are not merely different — the discrepancy is the factorial.
-/

open Finset

open TraceDistribution

/-! ## A multiset built from a multiplicity function -/





/-! ## The alternating binomial pair -/

theorem TraceDistribution.binom_powerSum_eq(n j : ℕ) (hj : j < n) :
    (Multiset.map (fun a => a ^ j) (binomEven n)).sum
      = (Multiset.map (fun a => a ^ j) (binomOdd n)).sum := by sorry
