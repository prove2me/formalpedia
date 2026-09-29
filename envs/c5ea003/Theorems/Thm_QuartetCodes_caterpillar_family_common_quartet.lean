-- Prove2me | Theorems.Thm_QuartetCodes_caterpillar_family_common_quartet
-- name    : QuartetCodes.caterpillar_family_common_quartet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:27:15.033498+00:00
-- url     : https://prove2.me/theorems/131450e2-1966-4d12-abd7-956a041b0567
-- title:
--   Doubly exponential upper bound.
-- statement:
--   **Doubly exponential upper bound.**  Any `k` caterpillars on more than `3 ^ (2 ^ k)` leaves
--   display a common quartet.  Together with `exponential_lower_bound` this brackets the least leaf
--   number forcing a common quartet between an exponential and a doubly exponential function of the
--   number of trees.
--
--   ```lean
--   theorem QuartetCodes.caterpillar_family_common_quartet{k : ℕ} (T : Fin k → Equiv.Perm (Fin n))
--       (hn : 3 ^ (2 ^ k) < n) :
--       ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
--         ∀ i : Fin k, qcode (T i) a b c d = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/QuartetCodesUpperBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/QuartetCodesUpperBound.lean#L368

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

theorem QuartetCodes.caterpillar_family_common_quartet{k : ℕ} (T : Fin k → Equiv.Perm (Fin n))
    (hn : 3 ^ (2 ^ k) < n) :
    ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ∀ i : Fin k, qcode (T i) a b c d = 0 := by sorry
