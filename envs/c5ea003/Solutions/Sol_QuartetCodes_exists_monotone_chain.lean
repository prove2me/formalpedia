-- Prove2me | solution 1 for QuartetCodes.exists_monotone_chain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:26:11.808856+00:00
-- url     : https://prove2.me/submissions/a9d5cd1b-8166-4314-8643-fa26973c36b7

-- Sol generated from Combinatorics/QuartetCodesUpperBound.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesUpperBound
import Theorems.Thm_QuartetCodes_decTo_lt_decTo
import Theorems.Thm_QuartetCodes_incTo_lt_incTo

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









lemma singleton_mem_incChainsTo (f : α → β) (i : α) : ({i} : Finset α) ∈ incChainsTo f i := by
  simp only [incChainsTo, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, by simp, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) (ne_of_lt hxy)
  · intro j hj; simp only [Finset.mem_singleton] at hj; exact le_of_eq hj

lemma singleton_mem_decChainsTo (f : α → β) (i : α) : ({i} : Finset α) ∈ decChainsTo f i := by
  simp only [decChainsTo, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨?_, by simp, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) (ne_of_lt hxy)
  · intro j hj; simp only [Finset.mem_singleton] at hj; exact le_of_eq hj

lemma one_le_incTo (f : α → β) (i : α) : 1 ≤ incTo f i := by
  have h : ({i} : Finset α).card ≤ incTo f i :=
    Finset.le_sup (f := Finset.card) (singleton_mem_incChainsTo f i)
  rwa [Finset.card_singleton] at h

lemma one_le_decTo (f : α → β) (i : α) : 1 ≤ decTo f i := by
  have h : ({i} : Finset α).card ≤ decTo f i :=
    Finset.le_sup (f := Finset.card) (singleton_mem_decChainsTo f i)
  rwa [Finset.card_singleton] at h






/-! ## Two caterpillars on ten leaves share a quartet -/


variable {n : ℕ}




/-! ## A doubly exponential upper bound for any number of trees -/




variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]



variable {n : ℕ}





open QuartetCodes in
theorem solution(f : α → β) (hf : Function.Injective f) {r : ℕ}
    (hcard : r * r < Fintype.card α) :
    ∃ t : Finset α, r < t.card ∧ (IsIncChain f t ∨ IsDecChain f t) := by
  by_contra hcon
  push_neg at hcon
  have hinc : ∀ i : α, incTo f i ≤ r := by
    intro i
    refine Finset.sup_le fun t ht => ?_
    simp only [incChainsTo, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    by_contra hgt
    exact (hcon t (by omega)).1 ht.1
  have hdec : ∀ i : α, decTo f i ≤ r := by
    intro i
    refine Finset.sup_le fun t ht => ?_
    simp only [decChainsTo, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    by_contra hgt
    exact (hcon t (by omega)).2 ht.1
  have hinj : ∀ i ∈ (Finset.univ : Finset α), ∀ j ∈ (Finset.univ : Finset α),
      (incTo f i, decTo f i) = (incTo f j, decTo f j) → i = j := by
    intro i _ j _ hpair
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · rcases lt_or_gt_of_ne (fun hfe => hne (hf hfe)) with hfv | hfv
      · exact absurd (congrArg Prod.fst hpair) (ne_of_lt (incTo_lt_incTo h hfv))
      · exact absurd (congrArg Prod.snd hpair) (ne_of_lt (decTo_lt_decTo h hfv))
    · rcases lt_or_gt_of_ne (fun hfe => hne (hf hfe)) with hfv | hfv
      · exact absurd (congrArg Prod.snd hpair).symm (ne_of_lt (decTo_lt_decTo h hfv))
      · exact absurd (congrArg Prod.fst hpair).symm (ne_of_lt (incTo_lt_incTo h hfv))
  have hmaps : ∀ i ∈ (Finset.univ : Finset α),
      (incTo f i, decTo f i) ∈ (Finset.Icc 1 r ×ˢ Finset.Icc 1 r : Finset (ℕ × ℕ)) := by
    intro i _
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨one_le_incTo f i, hinc i⟩, ⟨one_le_decTo f i, hdec i⟩⟩
  have hle := Finset.card_le_card_of_injOn (fun i => (incTo f i, decTo f i))
    (fun i hi => Finset.mem_coe.2 (hmaps i hi)) (fun i hi j hj h => hinj i hi j hj h)
  have hprod : (Finset.Icc 1 r ×ˢ Finset.Icc 1 r : Finset (ℕ × ℕ)).card = r * r := by
    simp [Finset.card_product, Nat.card_Icc]
  rw [Finset.card_univ, hprod] at hle
  omega
