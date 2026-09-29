-- Prove2me | solution 1 for Singmaster.mult_le_six_of_lt_million
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:53:22.131407+00:00
-- url     : https://prove2.me/submissions/bab90c67-6d59-4077-a477-12e5b00d66e8

-- Sol generated from Combinatorics/SingmasterMaxBelowMillion.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterMaxBelowMillion
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_centerOcc_card_le_one
import Theorems.Thm_Singmaster_leftInt_big_subsingleton
import Theorems.Thm_Singmaster_leftOcc_eq_insert
import Theorems.Thm_Singmaster_mem_leftOcc
import Theorems.Thm_Singmaster_mem_occ_iff
import Theorems.Thm_Singmaster_mult_eq_two_mul_add_center
import Theorems.Thm_Singmaster_mult_ne_five_or_seven_of_lt_large
import Theorems.Thm_Singmaster_mult_two
import Theorems.Thm_Singmaster_row_unique
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

/-- Column uniqueness in the column `k = 2`: the map `n ↦ C(n,2)` is injective. -/
theorem leftInt_two_subsingleton {t : ℕ} (ht : 2 ≤ t) :
    ((leftInt t).filter (fun p => p.2 = 2)).card ≤ 1 := by
  refine Finset.card_le_one.2 ?_
  rintro ⟨n, k⟩ h1 ⟨n', k'⟩ h2
  rw [mem_filter, mem_leftInt ht] at h1 h2
  obtain ⟨⟨⟨hk1, hv1⟩, _⟩, hk2⟩ := h1
  obtain ⟨⟨⟨hk1', hv1'⟩, _⟩, hk2'⟩ := h2
  simp only at hk2 hk2'
  subst hk2
  subst hk2'
  have : n = n' := row_unique (by norm_num) hk1 hk1' (by rw [hv1, hv1'])
  rw [this]

/-! ## The explicit box for the columns `k ≥ 3` -/





/-- **At most two left interior occurrences.**  For `2 ≤ t < 10^6` with `t ≠ 3003`. -/
theorem leftInt_card_le_two {t : ℕ} (ht : 2 ≤ t) (hlt : t < 1000000) (hne : t ≠ 3003) :
    (leftInt t).card ≤ 2 := by
  classical
  have hsplit :
      ((leftInt t).filter (fun p => p.2 = 2)).card
        + ((leftInt t).filter (fun p => ¬ p.2 = 2)).card = (leftInt t).card :=
    Finset.card_filter_add_card_filter_not _
  have h1 := leftInt_two_subsingleton (t := t) ht
  have h2 := leftInt_big_subsingleton ht hlt hne
  omega

/-! ## The multiplicity below `10^6` -/







open Singmaster in
theorem solution{t : ℕ} (ht : 2 ≤ t) (hlt : t < 1000000)
    (hne : t ≠ 3003) : mult t ≤ 6 := by
  rcases Nat.lt_or_ge t 3 with hsmall | ht3
  · have : t = 2 := by omega
    subst this
    rw [mult_two]
    norm_num
  · have hdec := mult_eq_two_add_two_mul_leftInt ht3
    have h1 := leftInt_card_le_two ht hlt hne
    have h2 := centerOcc_card_le_one (t := t) ht
    have h7 : mult t ≤ 7 := by omega
    have hne7 : mult t ≠ 7 :=
      (mult_ne_five_or_seven_of_lt_large ht (by omega)).2
    omega
