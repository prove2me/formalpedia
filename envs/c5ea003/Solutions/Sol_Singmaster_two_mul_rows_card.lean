-- Prove2me | solution 1 for Singmaster.two_mul_rows_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:57:21.111245+00:00
-- url     : https://prove2.me/submissions/39edaa5d-808b-462e-8f4c-cfec50bc29bf

-- Sol generated from Combinatorics/SingmasterRefinements.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_mem_occ_iff
import Theorems.Thm_Singmaster_row_solutions_le_two
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


theorem mem_rowOcc {n t k : ℕ} : k ∈ rowOcc n t ↔ k ≤ n ∧ n.choose k = t := by
  simp only [rowOcc, mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩




/-! ## `2` is the unique number of multiplicity one -/


/-! ## Central binomial coefficients occur at least three times -/


/-! ## The six-fold values form an infinite set -/




open Singmaster in
theorem solution{t : ℕ} (ht : 2 ≤ t) : mult t ≤ 2 * (rowsOf t).card := by
  classical
  refine Finset.card_le_mul_card_image (occ t) 2 ?_
  intro n _
  have hsub : ((occ t).filter (fun p => p.1 = n)).card ≤ (rowOcc n t).card := by
    refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
    · rintro ⟨m, k⟩ hp
      simp only [Finset.mem_coe, mem_filter] at hp
      obtain ⟨hmem, hm⟩ := hp
      rw [mem_occ_iff ht] at hmem
      subst hm
      simp only [Finset.mem_coe, mem_rowOcc]
      exact hmem
    · rintro ⟨m, k⟩ hp ⟨m', k'⟩ hp' hkk
      simp only [Finset.mem_coe, mem_filter] at hp hp'
      rw [Prod.mk.injEq]
      exact ⟨hp.2.trans hp'.2.symm, hkk⟩
  exact le_trans hsub (row_solutions_le_two n t)
