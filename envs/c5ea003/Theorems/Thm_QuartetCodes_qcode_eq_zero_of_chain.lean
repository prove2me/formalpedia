-- Prove2me | Theorems.Thm_QuartetCodes_qcode_eq_zero_of_chain
-- name    : QuartetCodes.qcode_eq_zero_of_chain
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:27:08.444022+00:00
-- url     : https://prove2.me/theorems/d9cd546c-0b86-491c-bd42-0aebc2c4f608
-- title:
--   Four leaves in increasing order on which the leaf order `π` is monotone carry the quartet
-- statement:
--   Four leaves in increasing order on which the leaf order `π` is monotone carry the quartet
--   type `0`.
--
--   ```lean
--   theorem QuartetCodes.qcode_eq_zero_of_chain{π : Equiv.Perm (Fin n)} {t : Finset (Fin n)} {a b c d : Fin n}
--       (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hd : d ∈ t) (hab : a < b) (hbc : b < c) (hcd : c < d)
--       (h : IsIncChain (fun x => π x) t ∨ IsDecChain (fun x => π x) t) :
--       qcode π a b c d = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/QuartetCodesUpperBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/QuartetCodesUpperBound.lean#L348

-- Thm stub generated from Combinatorics/QuartetCodesUpperBound.lean
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


















/-! ## Two caterpillars on ten leaves share a quartet -/


variable {n : ℕ}




/-! ## A doubly exponential upper bound for any number of trees -/




variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]



variable {n : ℕ}

theorem QuartetCodes.qcode_eq_zero_of_chain{π : Equiv.Perm (Fin n)} {t : Finset (Fin n)} {a b c d : Fin n}
    (ha : a ∈ t) (hb : b ∈ t) (hc : c ∈ t) (hd : d ∈ t) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h : IsIncChain (fun x => π x) t ∨ IsDecChain (fun x => π x) t) :
    qcode π a b c d = 0 := by sorry
