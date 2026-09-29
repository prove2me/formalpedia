-- Prove2me | solution 1 for Singmaster.mem_bigCols_of_leftInt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:25:58.566569+00:00
-- url     : https://prove2.me/submissions/e259ce16-e33f-450b-aa1c-ca0b1e6eb1e2

-- Sol generated from Combinatorics/SingmasterMaxBelowMillion.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterMaxBelowMillion
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_choose_two_le_choose
import Theorems.Thm_Singmaster_mem_leftOcc
import Theorems.Thm_Singmaster_mem_occ_iff
import Theorems.Thm_Singmaster_two_pow_le_choose
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



/-! ## At most one left interior occurrence in the column `k = 2` -/


/-! ## The explicit box for the columns `k ≥ 3` -/






/-! ## The multiplicity below `10^6` -/







open Singmaster in
theorem solution{t n k : ℕ} (ht : 2 ≤ t) (hlt : t < 1000000)
    (hmem : (n, k) ∈ leftInt t) (hk3 : 3 ≤ k) : (n, k) ∈ bigCols 1415 20 1000000 := by
  rw [mem_leftInt ht] at hmem
  obtain ⟨⟨hkn, hck⟩, hlt2, _⟩ := hmem
  have hkbound : k < 20 := by
    have h2k : 2 ^ k ≤ n.choose k := two_pow_le_choose (by omega)
    have hpow : (2 : ℕ) ^ k < 2 ^ 20 := by
      rw [hck] at h2k
      have : (2 : ℕ) ^ 20 = 1048576 := by norm_num
      omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hpow
  have hnbound : n < 1415 := by
    by_contra hcon
    push_neg at hcon
    have hc2 : n.choose 2 ≤ t := by
      rw [← hck]
      exact choose_two_le_choose (by omega) (by omega)
    have hmono : (1415 : ℕ).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hcon
    have hval : (1415 : ℕ).choose 2 = 1000405 := by
      rw [Nat.choose_two_right]
    omega
  have hdesc : n.descFactorial k = Nat.factorial k * t := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, hck]
  simp only [bigCols, mem_filter, mem_product, mem_range]
  refine ⟨⟨hnbound, hkbound⟩, hk3, hlt2, ?_⟩
  rw [hdesc]
  exact (Nat.mul_lt_mul_left (Nat.factorial_pos k)).2 hlt
