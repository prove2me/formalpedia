-- Prove2me | Theorems.Thm_Singmaster_two_mul_rows_card
-- name    : Singmaster.two_mul_rows_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:34:45.860006+00:00
-- url     : https://prove2.me/theorems/21674d14-3c2b-43c6-be40-1e781ccd1e40
-- title:
--   A value of high multiplicity must be spread over many rows.
-- statement:
--   **A value of high multiplicity must be spread over many rows.**  Since each row
--   contributes at most two positions, `N(t) ≤ 2 · #rows`.
--
--   ```lean
--   theorem Singmaster.two_mul_rows_card{t : ℕ} (ht : 2 ≤ t) : mult t ≤ 2 * (rowsOf t).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/SingmasterRefinements.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/SingmasterRefinements.lean#L100

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

theorem Singmaster.two_mul_rows_card{t : ℕ} (ht : 2 ≤ t) : mult t ≤ 2 * (rowsOf t).card := by sorry
