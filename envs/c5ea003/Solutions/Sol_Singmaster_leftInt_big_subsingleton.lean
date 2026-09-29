-- Prove2me | solution 1 for Singmaster.leftInt_big_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:27:35.268654+00:00
-- url     : https://prove2.me/submissions/64455c60-799b-4ddc-8be0-e3db64c3f7f7

-- Sol generated from Combinatorics/SingmasterMaxBelowMillion.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterCentralBinomialExtended
import Definitions.Def_Combinatorics_SingmasterExactCounts
import Definitions.Def_Combinatorics_SingmasterMaxBelowMillion
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Definitions.Def_Combinatorics_SingmasterParity
import Definitions.Def_Combinatorics_SingmasterRefinements
import Theorems.Thm_Singmaster_mem_bigCols_of_leftInt
import Theorems.Thm_Singmaster_mem_leftOcc
import Theorems.Thm_Singmaster_mem_occ_iff
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


set_option maxRecDepth 4000000 in
/-- **The kernel search.**  Among the `320` positions of Pascal's triangle with column
`k ≥ 3`, row `n < 1415` and value `< 10^6`, no two distinct ones carry the same value —
except the pair `C(15,5) = C(14,6) = 3003`.

This is a genuine exhaustive comparison of all `320²` pairs, type-checked by the Lean
kernel (`decide +kernel`, *not* `native_decide`). -/
theorem bigCols_pair_search :
    ∀ p ∈ bigCols 1415 20 1000000, ∀ q ∈ bigCols 1415 20 1000000,
      p.1.descFactorial p.2 / Nat.factorial p.2
        = q.1.descFactorial q.2 / Nat.factorial q.2 →
      p = q ∨ p.1.descFactorial p.2 / Nat.factorial p.2 = 3003 := by
  decide +kernel




/-! ## The multiplicity below `10^6` -/







open Singmaster in
theorem solution{t : ℕ} (ht : 2 ≤ t) (hlt : t < 1000000)
    (hne : t ≠ 3003) : ((leftInt t).filter (fun p => ¬ p.2 = 2)).card ≤ 1 := by
  refine Finset.card_le_one.2 ?_
  rintro ⟨n, k⟩ h1 ⟨n', k'⟩ h2
  rw [mem_filter] at h1 h2
  obtain ⟨hm1, hk1⟩ := h1
  obtain ⟨hm2, hk2⟩ := h2
  have hk3 : 3 ≤ k := by
    have := (mem_leftInt ht).1 hm1
    simp only at hk1
    omega
  have hk3' : 3 ≤ k' := by
    have := (mem_leftInt ht).1 hm2
    simp only at hk2
    omega
  have hb1 := mem_bigCols_of_leftInt ht hlt hm1 hk3
  have hb2 := mem_bigCols_of_leftInt ht hlt hm2 hk3'
  have hv1 : n.choose k = t := ((mem_leftInt ht).1 hm1).1.2
  have hv2 : n'.choose k' = t := ((mem_leftInt ht).1 hm2).1.2
  have he1 : n.descFactorial k / Nat.factorial k = t := by
    rw [← Nat.choose_eq_descFactorial_div_factorial, hv1]
  have he2 : n'.descFactorial k' / Nat.factorial k' = t := by
    rw [← Nat.choose_eq_descFactorial_div_factorial, hv2]
  rcases bigCols_pair_search (n, k) hb1 (n', k') hb2 (by rw [he1, he2]) with h | h
  · exact h
  · exact absurd (by rw [← he1]; exact h) hne
