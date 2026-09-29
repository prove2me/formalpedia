-- Prove2me | solution 1 for Singmaster.three_le_mult_centralBinom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:29:06.549635+00:00
-- url     : https://prove2.me/submissions/845bdb04-72b6-4553-8023-71802659a437

-- Sol generated from Combinatorics/SingmasterRefinements.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_choose_two_le_choose
import Theorems.Thm_Singmaster_mem_occ
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


/-! ## The six-fold values form an infinite set -/




open Singmaster in
theorem solution{m : ℕ} (hm : 2 ≤ m) : 3 ≤ mult ((2 * m).choose m) := by
  set n := 2 * m with hn
  set t := n.choose m with hT
  have hn4 : 4 ≤ n := by omega
  have hn2 : n.choose 2 ≤ t := choose_two_le_choose (by omega) (by omega)
  have hnt : n < t := by
    have h1 : n * 3 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
    have h2 : n.choose 2 = n * (n - 1) / 2 := Nat.choose_two_right n
    omega
  have m1 : (t, 1) ∈ occ t := mem_occ (by omega) (by omega) (Nat.choose_one_right t)
  have m2 : (t, t - 1) ∈ occ t := by
    refine mem_occ (by omega) (by omega) ?_
    have h := Nat.choose_symm (n := t) (k := 1) (by omega)
    rw [Nat.choose_one_right] at h
    exact h
  have m3 : (n, m) ∈ occ t := mem_occ (by omega) (by omega) rfl
  have hsub : ({(t, 1), (t, t - 1), (n, m)} : Finset (ℕ × ℕ)) ⊆ occ t := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨m1, m2, m3⟩
  have hcard : ({(t, 1), (t, t - 1), (n, m)} : Finset (ℕ × ℕ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.card_insert_of_notMem (by
        simp only [mem_singleton, Prod.mk.injEq]; omega),
      Finset.card_singleton]
  calc 3 = _ := hcard.symm
    _ ≤ mult t := card_le_card hsub
