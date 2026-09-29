-- Prove2me | solution 1 for QuartetCodes.decTo_lt_decTo
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:23:08.86741+00:00
-- url     : https://prove2.me/submissions/d47274f0-9ddd-4c37-a3fb-8913ad654632

-- Sol generated from Combinatorics/QuartetCodesUpperBound.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesUpperBound

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










lemma singleton_mem_decChainsTo (f : α → β) (i : α) : ({i} : Finset α) ∈ decChainsTo f i := by
  simp only [decChainsTo, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, by simp, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) (ne_of_lt hxy)
  · intro j hj; simp only [Finset.mem_singleton] at hj; exact le_of_eq hj








/-! ## Two caterpillars on ten leaves share a quartet -/


variable {n : ℕ}




/-! ## A doubly exponential upper bound for any number of trees -/




variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]



variable {n : ℕ}





open QuartetCodes in
theorem solution{f : α → β} {i j : α} (hij : i < j) (hf : f j < f i) :
    decTo f i < decTo f j := by
  obtain ⟨t, ht, hsup⟩ :=
    Finset.exists_mem_eq_sup (decChainsTo f i) ⟨{i}, singleton_mem_decChainsTo f i⟩ Finset.card
  simp only [decChainsTo, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  obtain ⟨hchain, hmem, hle⟩ := ht
  have hjt : j ∉ t := fun hj => absurd (hle j hj) (not_le.2 hij)
  have hnew : insert j t ∈ decChainsTo f j := by
    simp only [decChainsTo, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, Finset.mem_insert_self _ _, ?_⟩
    · intro x hx y hy hxy
      rcases Finset.mem_insert.1 hx with rfl | hx' <;> rcases Finset.mem_insert.1 hy with rfl | hy'
      · exact absurd rfl (ne_of_lt hxy)
      · exact absurd (hle y hy') (not_le.2 (lt_trans hij hxy))
      · have hxi : x ≤ i := hle x hx'
        rcases eq_or_lt_of_le hxi with rfl | hlt
        · exact hf
        · exact lt_trans hf (hchain x hx' i hmem hlt)
      · exact hchain x hx' y hy' hxy
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy'
      · exact le_refl _
      · exact le_of_lt (lt_of_le_of_lt (hle y hy') hij)
  have hcard : (insert j t).card = t.card + 1 := Finset.card_insert_of_notMem hjt
  have hbig : t.card + 1 ≤ decTo f j := by
    rw [← hcard]; exact Finset.le_sup hnew
  have hi' : decTo f i = t.card := hsup
  omega
