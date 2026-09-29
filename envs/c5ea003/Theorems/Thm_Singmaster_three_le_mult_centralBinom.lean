-- Prove2me | Theorems.Thm_Singmaster_three_le_mult_centralBinom
-- name    : Singmaster.three_le_mult_centralBinom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:33:18.25397+00:00
-- url     : https://prove2.me/theorems/9d445058-36ad-4bf6-9035-daa94ff01ae7
-- title:
--   Central binomial coefficients occur at least three times.
-- statement:
--   **Central binomial coefficients occur at least three times.**  The value
--   `t = C(2m,m)` sits at `(t,1)`, `(t,t-1)` and at the single central position `(2m,m)`.
--   The case `m = 2` is `6 = C(6,1) = C(6,5) = C(4,2)`, whose multiplicity is exactly `3`
--   by `Singmaster.mult_six`.
--
--   ```lean
--   theorem Singmaster.three_le_mult_centralBinom{m : ℕ} (hm : 2 ≤ m) : 3 ≤ mult ((2 * m).choose m) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterRefinements.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterRefinements.lean#L137

-- Thm stub generated from Combinatorics/SingmasterRefinements.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterRefinements
/-
# Refinements of the Singmaster occurrence theory

Second research cycle on top of `Combinatorics.SingmasterOccurrences` and
`Combinatorics.SingmasterFibonacci`.

* **Strict unimodality of a row** (`Singmaster.choose_lt_choose_right`): the left half
  of a Pascal row is strictly increasing.  This is the sharpest possible local
  statement, and it upgrades the "at most two positions per folded column" estimate of
  the first file into an exact *row* statement.
* **At most two entries per row** (`Singmaster.row_solutions_le_two`): for any value
  `t` and any row `n`, at most two entries of row `n` are equal to `t`.  Consequently a
  value of multiplicity `N` must be spread over at least `⌈N/2⌉` different rows
  (`Singmaster.two_mul_rows_card`).
* **`2` is the unique number of multiplicity one** (`Singmaster.mult_eq_one_iff`).
* **Central binomial coefficients occur at least three times**
  (`Singmaster.three_le_mult_centralBinom`), the pattern behind "6 occurs three times".
* **The six-fold values form an infinite set** (`Singmaster.setOf_six_infinite`),
  the set-theoretic form of the Fibonacci construction.
-/

open Finset

open Singmaster

/-! ## Strict unimodality of a Pascal row -/




/-! ## At most two entries per row -/






/-! ## `2` is the unique number of multiplicity one -/


/-! ## Central binomial coefficients occur at least three times -/

theorem Singmaster.three_le_mult_centralBinom{m : ℕ} (hm : 2 ≤ m) : 3 ≤ mult ((2 * m).choose m) := by sorry
