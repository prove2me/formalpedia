-- Prove2me | solution 1 for QuartetCodes.qcode_eq_zero_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:36:21.027408+00:00
-- url     : https://prove2.me/submissions/a67fcdeb-9378-4401-ab1e-5ca6bbf97ac2

-- Sol generated from Combinatorics/QuartetCodesUpperBound.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesUpperBound
import Theorems.Thm_QuartetCodes_code3_eq_zero_iff

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
theorem solution{π : Equiv.Perm (Fin n)} {t : Finset (Fin n)} {a b c d : Fin n}
    (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hd : d ∈ t) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h : IsIncChain (fun x => π x) t ∨ IsDecChain (fun x => π x) t) :
    qcode π a b c d = 0 := by
  unfold qcode
  refine (code3_eq_zero_iff _ _ _ _).2 ?_
  rcases h with h | h
  · left
    have h1 : (π a).val < (π b).val := h a ha b hb hab
    have h2 : (π b).val < (π c).val := h b hb c hc hbc
    have h3 : (π c).val < (π d).val := h c hc d hd hcd
    omega
  · right
    have h1 : (π b).val < (π a).val := h a ha b hb hab
    have h2 : (π c).val < (π b).val := h b hb c hc hbc
    have h3 : (π d).val < (π c).val := h c hc d hd hcd
    omega
