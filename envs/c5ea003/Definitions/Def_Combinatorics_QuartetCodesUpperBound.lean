-- Prove2me | Definitions.Def_Combinatorics_QuartetCodesUpperBound
-- name    : Combinatorics_QuartetCodesUpperBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:48:18.960883+00:00
-- url     : https://prove2.me/theorems/7548fee2-6301-46a5-86b1-ac6ac8b565e1
-- title:
--   Aether Catalog definitions — Combinatorics_QuartetCodesUpperBound
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.QuartetCodesUpperBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/QuartetCodesUpperBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes

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

namespace QuartetCodes

/-! ## Erdős–Szekeres, self-contained -/

section ErdosSzekeres

variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]

/-- `t` is a strictly increasing chain for `f`. -/
def IsIncChain (f : α → β) (t : Finset α) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, x < y → f x < f y

/-- `t` is a strictly decreasing chain for `f`. -/
def IsDecChain (f : α → β) (t : Finset α) : Prop :=
  ∀ x ∈ t, ∀ y ∈ t, x < y → f y < f x

instance (f : α → β) (t : Finset α) : Decidable (IsIncChain f t) := by
  unfold IsIncChain; infer_instance

instance (f : α → β) (t : Finset α) : Decidable (IsDecChain f t) := by
  unfold IsDecChain; infer_instance

/-- The increasing chains ending at `i`. -/
def incChainsTo (f : α → β) (i : α) : Finset (Finset α) :=
  {t : Finset α | IsIncChain f t ∧ i ∈ t ∧ ∀ j ∈ t, j ≤ i}

/-- The decreasing chains ending at `i`. -/
def decChainsTo (f : α → β) (i : α) : Finset (Finset α) :=
  {t : Finset α | IsDecChain f t ∧ i ∈ t ∧ ∀ j ∈ t, j ≤ i}

/-- Length of the longest increasing chain ending at `i`. -/
def incTo (f : α → β) (i : α) : ℕ := (incChainsTo f i).sup Finset.card

/-- Length of the longest decreasing chain ending at `i`. -/
def decTo (f : α → β) (i : α) : ℕ := (decChainsTo f i).sup Finset.card









end ErdosSzekeres

/-! ## Two caterpillars on ten leaves share a quartet -/

section PairUpperBound

variable {n : ℕ}



end PairUpperBound

/-! ## A doubly exponential upper bound for any number of trees -/

section FamilyUpperBound



variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]



variable {n : ℕ}



end FamilyUpperBound

end QuartetCodes


