-- Prove2me | Theorems.Thm_Singmaster_mult_24310
-- name    : Singmaster.mult_24310
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:33:51.207329+00:00
-- url     : https://prove2.me/theorems/2a289e32-1028-4104-a20c-bd4e2c2480c3
-- title:
--   `24310 = C(221,2) = C(221,219) = C(17,8) = C(17,9) = C(24310,1) = C(24310,24309)`
-- statement:
--   `24310 = C(221,2) = C(221,219) = C(17,8) = C(17,9) = C(24310,1) = C(24310,24309)`
--   occurs **exactly** six times.
--
--   This value was out of reach of the box search of `Combinatorics.SingmasterExactCounts`
--   (its box has side `221`); here the upper bound comes from
--   `Singmaster.mult_le_six_of_lt_million` and the lower bound from two explicit left
--   interior occurrences.
--
--   ```lean
--   theorem Singmaster.mult_24310: mult 24310 = 6 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterMaxBelowMillion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterMaxBelowMillion.lean#L262

-- Thm stub generated from Combinatorics/SingmasterMaxBelowMillion.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterMaxBelowMillion
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
/-
# The maximum multiplicity below `10^6` is `8`, attained only at `3003`

Seventh research cycle.  `Combinatorics.SingmasterExactCounts` proved `N(3003) = 8`;
this file proves that below `10^6` *nothing else even comes close*: every other number
occurs at most six times.  In particular `3003` is the unique number below `10^6` of
multiplicity eight, which is the sub-conjecture 6b of `FUTURE_DIRECTIONS.md`.

## The mechanism

The reflection decomposition of `Combinatorics.SingmasterParity` writes

`N(t) = 2 · #(left occurrences) + #(central occurrences)`,

and for `t ≥ 3` exactly one left occurrence is the trivial one `C(t,1) = t`, so

`N(t) = 2 + 2 · #(left interior occurrences) + #(central occurrences)`
  (`Singmaster.mult_eq_two_add_two_mul_leftInt`).

A left interior occurrence has column `k ≥ 2` and `2k < n`, and column uniqueness makes
its column determine its row.  Therefore:

* there is **at most one** left interior occurrence in the column `k = 2`;
* if `t < 10^6` then any left interior occurrence with `k ≥ 3` has `k < 20`
  (because `2^k ≤ C(n,k) = t`) and `n < 1415` (because `C(n,2) ≤ C(n,k) = t` and
  `C(1415,2) = 1000405 > 10^6`), i.e. it lies in the explicit `1415 × 20` box
  `Singmaster.bigCols`;
* a single kernel search over that box (`Singmaster.bigCols_pair_search`, `320` entries,
  all pairs compared) shows that **no value below `10^6` occurs twice with column
  `≥ 3`, except `3003 = C(15,5) = C(14,6)`**.

Hence for `t < 10^6`, `t ≠ 3003`, there are at most `1 + 1 = 2` left interior
occurrences, so `N(t) ≤ 2 + 4 + 1 = 7`; and `N(t) = 7` is impossible by
`Combinatorics.SingmasterCentralBinomialExtended.mult_ne_five_or_seven_of_lt_large`.

## Results

* `Singmaster.mult_eq_two_add_two_mul_leftInt` — the refined decomposition;
* `Singmaster.bigCols_pair_search` — the kernel search;
* `Singmaster.leftInt_card_le_two` — at most two left interior occurrences below `10^6`
  away from `3003`;
* `Singmaster.mult_le_six_of_lt_million` — **every `t` with `2 ≤ t < 10^6` and
  `t ≠ 3003` occurs at most six times**;
* `Singmaster.mult_eq_eight_iff_of_lt_million` — **`3003` is the unique number below
  `10^6` occurring exactly eight times**;
* `Singmaster.mult_le_eight_of_lt_million` — the multiplicity function is bounded by `8`
  on `[2, 10^6)`, a Singmaster-type bound with the conjectured optimal constant on that
  range;
* `Singmaster.mult_24310` — `N(24310) = 6`, a value out of reach of the earlier box
  search, obtained by combining the new upper bound with two explicit occurrences.
-/

open Finset

set_option maxRecDepth 100000

open Singmaster

/-! ## Left interior occurrences -/





/-! ## At most one left interior occurrence in the column `k = 2` -/


/-! ## The explicit box for the columns `k ≥ 3` -/






/-! ## The multiplicity below `10^6` -/

theorem Singmaster.mult_24310: mult 24310 = 6 := by sorry
