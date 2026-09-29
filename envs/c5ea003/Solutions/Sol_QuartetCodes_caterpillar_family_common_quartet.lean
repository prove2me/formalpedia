-- Prove2me | solution 1 for QuartetCodes.caterpillar_family_common_quartet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:50:39.183873+00:00
-- url     : https://prove2.me/submissions/9b362396-50f1-45b2-8068-a21dd694231c

-- Sol generated from Combinatorics/QuartetCodesUpperBound.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesUpperBound
import Theorems.Thm_QuartetCodes_exists_common_monotone
import Theorems.Thm_QuartetCodes_qcode_eq_zero_of_chain

/-!
# A matching upper bound: two caterpillars on ten leaves always share a quartet

The companion file `Combinatorics.QuartetCodes` produces, by a first-moment count in ternary
quartet-signature space, exponentially many caterpillar trees with *no* common quartet.  This file
proves the opposite kind of statement for two trees, and is therefore the boundary of the
lower-bound method: **any two caterpillars on at least ten leaves display a common quartet**.

The engine is a self-contained proof of the Erdős–Szekeres theorem in the shape we need: an
injective map on a linearly ordered fintype with more than `9` elements has a strictly monotone
(increasing or decreasing) subset of size four.  Combined with the observation that a quadruple of
leaves ordered the same way — or in exactly opposite ways — by two caterpillars carries the same
quartet type, this yields the upper bound.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Since the first-moment bound needs `n^4 < 3^m`, it is vacuous for two trees (`m = 1`).  Conjecture:
for two trees a *constant* number of leaves already forces a common quartet, and Erdős–Szekeres
supplies the constant.

## Experiment (Experimenter)
Exhaustive search over all `120^2` pairs of leaf orders on five leaves found pairs with no common
quartet; over all pairs on six leaves none exists (see `ComputationalEvidence.md`).  So the true
threshold for two caterpillars is `6`; Erdős–Szekeres with `r = s = 3` proves `10`, and the
five-leaf pair `not_isAgreementThreshold_five_two` shows the truth is at least `6`.

## Analysis (Analyst)
The gap `6 ≤ h_cat(2) ≤ 10` isolates exactly what the monotone-subsequence argument loses: it
insists on a quadruple that is monotone, whereas a common quartet only needs the *unordered*
`2 + 2` split to coincide.

## Critique (Critic)
The upper bound is proved for caterpillars (leaf orders), the same class in which the lower bound
constructs its avoiding families, so the two bounds are comparable.  Nothing here is proved by
`decide` on the whole statement: the Erdős–Szekeres step is a genuine pigeonhole over the pair
`(longest increasing chain, longest decreasing chain)`.
-/

open Finset

open QuartetCodes

/-! ## Erdős–Szekeres, self-contained -/


variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]


















/-! ## Two caterpillars on ten leaves share a quartet -/


variable {n : ℕ}

/-- Four leaves listed in increasing order of a monotone (or antitone) chain. -/
lemma exists_four_of_card {t : Finset (Fin n)} (ht : 4 ≤ t.card) :
    ∃ x y z w : Fin n, x ∈ t ∧ y ∈ t ∧ z ∈ t ∧ w ∈ t ∧ x < y ∧ y < z ∧ z < w := by
  obtain ⟨t', hsub, hcard⟩ := Finset.exists_subset_card_eq ht
  let e := t'.orderIsoOfFin hcard
  refine ⟨(e 0 : Fin n), (e 1 : Fin n), (e 2 : Fin n), (e 3 : Fin n),
    hsub (e 0).2, hsub (e 1).2, hsub (e 2).2, hsub (e 3).2, ?_, ?_, ?_⟩
  · exact (Subtype.coe_lt_coe).2 (e.lt_iff_lt.2 (by decide))
  · exact (Subtype.coe_lt_coe).2 (e.lt_iff_lt.2 (by decide))
  · exact (Subtype.coe_lt_coe).2 (e.lt_iff_lt.2 (by decide))



/-! ## A doubly exponential upper bound for any number of trees -/




variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]



variable {n : ℕ}





open QuartetCodes in
theorem solution{k : ℕ} (T : Fin k → Equiv.Perm (Fin n))
    (hn : 3 ^ (2 ^ k) < n) :
    ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ∀ i : Fin k, qcode (T i) a b c d = 0 := by
  classical
  set F : ℕ → Fin n → Fin n := fun i => if h : i < k then ⇑(T ⟨i, h⟩) else id with hFdef
  have hF : ∀ i, Function.Injective (F i) := by
    intro i
    by_cases h : i < k
    · simpa [hFdef, h] using (T ⟨i, h⟩).injective
    · simpa [hFdef, h] using Function.injective_id
  have hcard : 3 ^ (2 ^ k) < (Finset.univ : Finset (Fin n)).card := by simpa using hn
  obtain ⟨t, _, htcard, hmono⟩ := exists_common_monotone F hF k Finset.univ hcard
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hbc, hcd⟩ := exists_four_of_card (by omega : 4 ≤ t.card)
  refine ⟨a, b, c, d, ne_of_lt hab, ne_of_lt (hab.trans hbc), ne_of_lt (hab.trans (hbc.trans hcd)),
    ne_of_lt hbc, ne_of_lt (hbc.trans hcd), ne_of_lt hcd, fun i => ?_⟩
  have hi := hmono i.val i.isLt
  have hFi : F i.val = ⇑(T i) := by
    simp only [hFdef, dif_pos i.isLt]
  rw [hFi] at hi
  exact qcode_eq_zero_of_chain ha hb hc hd hab hbc hcd hi
