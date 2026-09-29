-- Prove2me | Definitions.Def_Combinatorics_SingmasterRefinements
-- name    : Combinatorics_SingmasterRefinements
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:50:37.026728+00:00
-- url     : https://prove2.me/theorems/a067f124-bfee-4ab3-b54e-5c9def30542d
-- title:
--   Aether Catalog definitions — Combinatorics_SingmasterRefinements
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.SingmasterRefinements`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/SingmasterRefinements.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
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

namespace Singmaster

/-! ## Strict unimodality of a Pascal row -/




/-! ## At most two entries per row -/

/-- The set of columns of row `n` carrying the value `t`. -/
def rowOcc (n t : ℕ) : Finset ℕ := (range (n + 1)).filter (fun k => n.choose k = t)



/-- The rows in which `t` occurs. -/
def rowsOf (t : ℕ) : Finset ℕ := (occ t).image Prod.fst


/-! ## `2` is the unique number of multiplicity one -/


/-! ## Central binomial coefficients occur at least three times -/


/-! ## The six-fold values form an infinite set -/



end Singmaster


