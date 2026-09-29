-- Prove2me | Theorems.Thm_Singmaster_mult_centralBinom_eq_three_cubic
-- name    : Singmaster.mult_centralBinom_eq_three_cubic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:32:55.26345+00:00
-- url     : https://prove2.me/theorems/adf35b59-4c2e-4181-b815-5361ff4cc6af
-- title:
--   Effective criterion for `N(C(2m,m)) = 3`, cubic form.
-- statement:
--   **Effective criterion for `N(C(2m,m)) = 3`, cubic form.**  Suppose `m ≥ 3`,
--   `t = C(2m,m)`, and
--
--   `8t + 1` is strictly between the consecutive squares `s²` and `(s+1)²`, so `t` is not
--     triangular and the column `k = 2` is empty,
--   `C(N,3)` already exceeds `t` (so every remaining escape row is `< N`),
--   no entry with row in `(2m, N)` and column in `[3, m-1]` equals `t`.
--
--   Then `t` occurs exactly three times: at `(t,1)`, `(t,t-1)` and at the central position
--   `(2m,m)`.
--
--   ```lean
--   theorem Singmaster.mult_centralBinom_eq_three_cubic{m N t s : ℕ} (hm : 3 ≤ m)
--       (hval : (2 * m).choose m = t) (hN : t < N.choose 3)
--       (hs1 : s * s < 8 * t + 1) (hs2 : 8 * t + 1 < (s + 1) * (s + 1))
--       (H : NoCubicRepeat m N t) : mult t = 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterCentralBinomialExtended.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterCentralBinomialExtended.lean#L161

-- Thm stub generated from Combinatorics/SingmasterCentralBinomialExtended.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomial
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
/-
# A cubic search window: `N(C(2m,m)) = 3` up to `m = 20`, and no fives or sevens below
# `538257874440`

Sixth research cycle.  `Combinatorics.SingmasterCentralBinomial` reduced the open
question *"does any number occur exactly five or exactly seven times?"* to the single
sequence of central binomial coefficients and made the reduction effective: for
`t = C(2m,m)` the multiplicity is `3` as soon as no interior entry `C(n,k) = t` occurs
in a row `2m < n < N` with `N ≈ √(2t)` and `2 ≤ k ≤ n/2`.  Executing that quadratic
search cost `(N - 2m) · (N/2)` kernel tests and stopped at `m = 10`.

This file removes both factors of the search box.

## Two structural reductions

* **The column collapse** (`Singmaster.column_lt_of_choose_eq_centralBinom`).  In the
  escape window the column index is *tiny*: if `2k ≤ n`, `n > 2m` and
  `C(n,k) = C(2m,m)`, then `k < m`.  Indeed `C(2k,k) ≤ C(n,k)` (monotonicity in the
  row) and `m ↦ C(2m,m)` is strictly increasing, so `k ≥ m` would force
  `C(2m,m) ≤ C(2k,k) ≤ C(n,k) = C(2m,m)` with a strict inequality somewhere (from
  `k > m`, or from `n > 2m` when `k = m`).  So the columns run over `[3, m-1]`, a strip
  of height `m`, instead of a triangle of height `N/2`.

* **The triangular obstruction** (`Singmaster.choose_two_ne_of_not_sq`).  The column
  `k = 2` is the one that forces the large window `N ≈ √(2t)`, and it need not be
  searched at all: `C(n,2) = t` happens iff `t` is a triangular number, i.e. iff
  `8t + 1` is a perfect square.  A single square test therefore eliminates the whole
  column `k = 2`, after which every remaining entry satisfies `C(n,3) ≤ t` and the row
  window shrinks from `√(2t)` to `(6t)^{1/3}`.

For `m = 20` the box shrinks from `524248 × 262124` to `9347 × 17`: a saving of more
than nine orders of magnitude, which is what makes the kernel verification of
`m = 11, …, 20` possible.

## Results

* `Singmaster.two_mul_choose_two`, `Singmaster.choose_two_ne_of_not_sq` — the
  triangular obstruction;
* `Singmaster.column_lt_of_choose_eq_centralBinom` — the column collapse;
* `Singmaster.mult_centralBinom_eq_three_cubic` — the resulting criterion;
* `Singmaster.mult_centralBinom_eq_three_of_le_twenty` — `N(C(2m,m)) = 3` for every
  `2 ≤ m ≤ 20`, i.e. up to `C(40,20) = 137846528820`;
* `Singmaster.mult_ne_five_or_seven_of_lt_large` — **unconditionally, no `t` with
  `2 ≤ t < 538257874440 = C(42,21)` occurs exactly five or exactly seven times**,
  extending the previous range `705432` by a factor of more than `700000`.
-/

open Finset

open Singmaster

/-! ## The triangular obstruction: the column `k = 2` -/



/-! ## The column collapse -/


/-! ## Comparison lemmas for the truncated box -/



/-! ## The criterion -/

theorem Singmaster.mult_centralBinom_eq_three_cubic{m N t s : ℕ} (hm : 3 ≤ m)
    (hval : (2 * m).choose m = t) (hN : t < N.choose 3)
    (hs1 : s * s < 8 * t + 1) (hs2 : 8 * t + 1 < (s + 1) * (s + 1))
    (H : NoCubicRepeat m N t) : mult t = 3 := by sorry
