-- Prove2me | solution 1 for QuartetCodes.exists_monotone_chain_subset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:28:20.298601+00:00
-- url     : https://prove2.me/submissions/7505a1f1-bebd-433b-9f9c-4d2aba97eba9

-- Sol generated from Combinatorics/QuartetCodesUpperBound.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesUpperBound
import Theorems.Thm_QuartetCodes_exists_monotone_chain

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




/-! ## A doubly exponential upper bound for any number of trees -/




variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]



variable {n : ℕ}





open QuartetCodes in
omit [Fintype α] in
theorem solution(f : α → β) (hf : Function.Injective f) {r : ℕ}
    {S : Finset α} (hcard : r * r < S.card) :
    ∃ t ⊆ S, r < t.card ∧ (IsIncChain f t ∨ IsDecChain f t) := by
  have hcard' : r * r < Fintype.card {x // x ∈ S} := by rwa [Fintype.card_coe]
  obtain ⟨t', ht', hchain⟩ := exists_monotone_chain (fun x : {x // x ∈ S} => f x.1)
    (fun x y h => Subtype.ext (hf h)) hcard'
  refine ⟨Finset.image (fun x : {x // x ∈ S} => (x : α)) t', ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hy
    exact x.2
  · rwa [Finset.card_image_of_injective _ Subtype.coe_injective]
  · rcases hchain with h | h
    · refine Or.inl fun x hx y hy hxy => ?_
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
      exact h x' hx' y' hy' (Subtype.coe_lt_coe.1 hxy)
    · refine Or.inr fun x hx y hy hxy => ?_
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
      exact h x' hx' y' hy' (Subtype.coe_lt_coe.1 hxy)
