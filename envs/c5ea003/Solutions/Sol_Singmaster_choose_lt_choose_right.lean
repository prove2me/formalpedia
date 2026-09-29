-- Prove2me | solution 1 for Singmaster.choose_lt_choose_right
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:01:12.369467+00:00
-- url     : https://prove2.me/submissions/38c5bb56-6ed7-4f7b-9979-a57264407638

-- Sol generated from Combinatorics/SingmasterRefinements.lean
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

/-- One step of strict increase in the left half of a row. -/
theorem choose_lt_choose_succ_right {n k : ℕ} (h : 2 * (k + 1) ≤ n) :
    n.choose k < n.choose (k + 1) := by
  have e := Nat.choose_succ_right_eq n k
  have hpos : 0 < n.choose k := Nat.choose_pos (by omega)
  have h1 : n.choose k * (k + 1) < n.choose k * (n - k) :=
    Nat.mul_lt_mul_of_pos_left (by omega) hpos
  have h2 : n.choose k * (k + 1) < n.choose (k + 1) * (k + 1) := by omega
  exact Nat.lt_of_mul_lt_mul_right h2



/-! ## At most two entries per row -/






/-! ## `2` is the unique number of multiplicity one -/


/-! ## Central binomial coefficients occur at least three times -/


/-! ## The six-fold values form an infinite set -/




open Singmaster in
theorem solution{n j j' : ℕ} (hjj : j < j') (h : 2 * j' ≤ n) :
    n.choose j < n.choose j' := by
  induction j' with
  | zero => omega
  | succ p ih =>
    rcases Nat.lt_or_ge j p with hp | hp
    · exact lt_trans (ih hp (by omega)) (choose_lt_choose_succ_right (by omega))
    · have hjp : j = p := by omega
      subst hjp
      exact choose_lt_choose_succ_right (by omega)
