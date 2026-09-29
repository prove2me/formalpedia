-- Prove2me | Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
-- name    : Combinatorics_SingmasterCentralBinomialExtended
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:55:19.016264+00:00
-- url     : https://prove2.me/theorems/a6c33239-7284-4535-9496-03dea0974b08
-- title:
--   Aether Catalog definitions — Combinatorics_SingmasterCentralBinomialExtended
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.SingmasterCentralBinomialExtended`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/SingmasterCentralBinomialExtended.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomial
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

namespace Singmaster

/-! ## The triangular obstruction: the column `k = 2` -/



/-! ## The column collapse -/


/-! ## Comparison lemmas for the truncated box -/



/-! ## The criterion -/

/-- The cubic search predicate: no entry `C(n,k) = t` with `2m < n < N` and
`3 ≤ k ≤ m - 1`.  As before the test is phrased through `Nat.descFactorial`, which
costs `k` multiplications instead of `C(n,k)` additions. -/
abbrev NoCubicRepeat (m N t : ℕ) : Prop :=
  ∀ n ∈ Finset.Ico (2 * m + 1) N, ∀ k ∈ Finset.Icc 3 (m - 1),
    n.descFactorial k ≠ Nat.factorial k * t



/-! ## Executing the criterion for `11 ≤ m ≤ 20`

Each search runs over the rectangle `2m < n < (6t)^{1/3}`, `3 ≤ k ≤ m - 1`; the largest
is `40 < n < 9388`, `3 ≤ k ≤ 19` for `m = 20`.  Every step is a kernel computation:
`decide +kernel` type-checks the Boolean evaluation in the kernel, it is *not*
`native_decide`. -/












/-! ## Unconditional consequences below `C(42,21) = 538257874440` -/



end Singmaster


