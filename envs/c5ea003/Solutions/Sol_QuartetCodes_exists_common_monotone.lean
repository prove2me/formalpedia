-- Prove2me | solution 1 for QuartetCodes.exists_common_monotone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:36:20.465087+00:00
-- url     : https://prove2.me/submissions/033533a2-5c71-404c-98b8-4cbad97fbc0b

-- Sol generated from Combinatorics/QuartetCodesUpperBound.lean
import Mathlib
import Definitions.Def_Combinatorics_QuartetCodes
import Definitions.Def_Combinatorics_QuartetCodesUpperBound
import Theorems.Thm_QuartetCodes_exists_monotone_chain_subset

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


lemma IsIncChain.mono {α β : Type*} [LinearOrder α] [LinearOrder β] {f : α → β}
    {t s : Finset α} (h : IsIncChain f s) (hts : t ⊆ s) : IsIncChain f t :=
  fun x hx y hy hxy => h x (hts hx) y (hts hy) hxy

lemma IsDecChain.mono {α β : Type*} [LinearOrder α] [LinearOrder β] {f : α → β}
    {t s : Finset α} (h : IsDecChain f s) (hts : t ⊆ s) : IsDecChain f t :=
  fun x hx y hy hxy => h x (hts hx) y (hts hy) hxy

variable {α β : Type*} [LinearOrder α] [Fintype α] [DecidableEq α] [LinearOrder β]



variable {n : ℕ}





open QuartetCodes in
omit [Fintype α] in
theorem solution(F : ℕ → α → β) (hF : ∀ i, Function.Injective (F i)) :
    ∀ (k : ℕ) (S : Finset α), 3 ^ (2 ^ k) < S.card →
      ∃ t ⊆ S, 3 < t.card ∧ ∀ i < k, (IsIncChain (F i) t ∨ IsDecChain (F i) t) := by
  intro k
  induction k with
  | zero =>
    intro S hS
    exact ⟨S, Finset.Subset.refl S, by simpa using hS, fun i hi => absurd hi (by omega)⟩
  | succ k ih =>
    intro S hS
    have hpow : (3 : ℕ) ^ (2 ^ k) * 3 ^ (2 ^ k) < S.card := by
      have : (3 : ℕ) ^ (2 ^ k) * 3 ^ (2 ^ k) = 3 ^ (2 ^ (k + 1)) := by
        rw [← pow_add, pow_succ]
        ring_nf
      rw [this]; exact hS
    obtain ⟨t₁, ht₁S, ht₁card, ht₁chain⟩ := exists_monotone_chain_subset (F k) (hF k) hpow
    obtain ⟨t, hts, htcard, hmono⟩ := ih t₁ ht₁card
    refine ⟨t, hts.trans ht₁S, htcard, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · exact hmono i hlt
    · rcases ht₁chain with h | h
      · exact Or.inl (IsIncChain.mono h hts)
      · exact Or.inr (IsDecChain.mono h hts)
