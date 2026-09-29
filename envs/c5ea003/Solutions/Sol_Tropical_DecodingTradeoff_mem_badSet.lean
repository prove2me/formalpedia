-- Prove2me | solution 1 for Tropical.DecodingTradeoff.mem_badSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:31:06.399794+00:00
-- url     : https://prove2.me/submissions/27f5e78d-8c9f-47c0-b0de-8463f23c734b

-- Sol generated from Tropical/DecodingTradeoff/Environment.lean
import Mathlib
import Definitions.Def_Tropical_DecodingTradeoff_Environment
/-
# The Bernoulli environment: the probabilistic endpoint of the decoding trade-off

This file builds, from scratch and with no measure theory, the finite Bernoulli product
measure on environments `ω : Fin n → Bool`.  Here `ω i = true` means "step `i` of the
tropical chain is *informative*" (its transfer matrix has small diameter), and
`ω i = false` means the step is *uninformative*.

The decoder of `Tropical.DecodingTradeoff.Tradeoff` with window length `b` fails at a
position only if an entire window of `b` consecutive steps is uninformative.  This file
computes the probability of that event exactly and bounds it from both sides.

## Main results

* `Prob_univ` — the weights `wt p` form a probability distribution (total mass `1`).
* `Prob_badWindow` — the probability that a whole window of length `b` is uninformative
  is **exactly** `(1 - p) ^ b`.
* `prob_failSet_le` — union bound: `Prob p (failSet b) ≤ (n + 1 - b) * (1 - p) ^ b`.
* `prob_failSet_ge` — matching lower bound: `(1 - p) ^ b ≤ Prob p (failSet b)`.

The upper and lower bounds differ only by the polynomial factor `n + 1 - b`; this is
what makes the converse (cost lower bound) of the trade-off possible.
-/


open Finset

open Tropical.DecodingTradeoff

/-! ## §0. Two elementary facts about sums of nonnegative terms -/



/-! ## §1. Environments and the Bernoulli product weight -/

variable {n : ℕ}








/-! ## §2. Uninformative windows -/

















open Tropical.DecodingTradeoff in
theorem solution{n : ℕ} {W : Finset (Fin n)} (ω : Fin n → Bool) :
    ω ∈ badSet n W ↔ ∀ x ∈ W, ω x = false := by
  classical
  simp only [badSet, Fintype.mem_piFinset]
  constructor
  · intro h x hx
    have := h x
    rw [if_pos hx] at this
    simpa using this
  · intro h x
    by_cases hx : x ∈ W
    · rw [if_pos hx]; simp [h x hx]
    · rw [if_neg hx]; exact Finset.mem_univ _
