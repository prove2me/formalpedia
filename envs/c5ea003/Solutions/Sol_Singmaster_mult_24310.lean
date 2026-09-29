-- Prove2me | solution 1 for Singmaster.mult_24310
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:54:46.968789+00:00
-- url     : https://prove2.me/submissions/61bd1249-32ce-418f-9460-e78315726470

-- Sol generated from Combinatorics/SingmasterMaxBelowMillion.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterMaxBelowMillion
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_choose_eq_iff_descFactorial
import Theorems.Thm_Singmaster_leftOcc_eq_insert
import Theorems.Thm_Singmaster_mem_leftOcc
import Theorems.Thm_Singmaster_mem_occ_iff
import Theorems.Thm_Singmaster_mult_eq_two_mul_add_center
import Theorems.Thm_Singmaster_mult_le_six_of_lt_million
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


theorem mem_leftInt {t n k : ℕ} (ht : 2 ≤ t) :
    (n, k) ∈ leftInt t ↔ (k ≤ n ∧ n.choose k = t) ∧ 2 * k < n ∧ 2 ≤ k := by
  simp only [leftInt, mem_filter, mem_leftOcc, mem_occ_iff ht]
  tauto


/-- **Refined reflection decomposition.**  For `t ≥ 3`,
`N(t) = 2 + 2·#(left interior occurrences) + #(central occurrences)`. -/
theorem mult_eq_two_add_two_mul_leftInt {t : ℕ} (ht : 3 ≤ t) :
    mult t = 2 + 2 * (leftInt t).card + (centerOcc t).card := by
  have ht2 : 2 ≤ t := by omega
  have hnot : (t, 1) ∉ leftInt t := by
    intro hmem
    rw [mem_leftInt ht2] at hmem
    omega
  have hcard : (leftOcc t).card = 1 + (leftInt t).card := by
    rw [leftOcc_eq_insert ht, Finset.card_insert_of_notMem hnot]
    omega
  rw [mult_eq_two_mul_add_center ht2, hcard]
  ring

/-! ## At most one left interior occurrence in the column `k = 2` -/


/-! ## The explicit box for the columns `k ≥ 3` -/






/-! ## The multiplicity below `10^6` -/







open Singmaster in
theorem solution: mult 24310 = 6 := by
  have hub := mult_le_six_of_lt_million (t := 24310) (by norm_num) (by norm_num)
    (by norm_num)
  have hmem1 : (221, 2) ∈ leftInt 24310 := by
    rw [mem_leftInt (by norm_num)]
    exact ⟨⟨by norm_num, by norm_num [Nat.choose_two_right]⟩, by norm_num, by norm_num⟩
  have hmem2 : (17, 8) ∈ leftInt 24310 := by
    rw [mem_leftInt (by norm_num)]
    exact ⟨⟨by norm_num, choose_eq_iff_descFactorial.2 (by decide)⟩, by norm_num,
      by norm_num⟩
  have hsub : ({(221, 2), (17, 8)} : Finset (ℕ × ℕ)) ⊆ leftInt 24310 := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hmem1
    · exact hmem2
  have hcard : ({(221, 2), (17, 8)} : Finset (ℕ × ℕ)).card = 2 := by decide
  have h2 : 2 ≤ (leftInt 24310).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hdec := mult_eq_two_add_two_mul_leftInt (t := 24310) (by norm_num)
  omega
