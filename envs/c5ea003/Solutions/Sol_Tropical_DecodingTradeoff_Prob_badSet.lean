-- Prove2me | solution 1 for Tropical.DecodingTradeoff.Prob_badSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:31:05.922268+00:00
-- url     : https://prove2.me/submissions/b3cadb48-4b01-4816-a44f-a0d0c66f0fb5

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
theorem solution(p : ℝ) {n : ℕ} (W : Finset (Fin n)) :
    Prob p (badSet n W) = (1 - p) ^ W.card := by
  classical
  have h := Finset.prod_univ_sum (ι := Fin n) (κ := fun _ => Bool)
      (fun x : Fin n => if x ∈ W then ({false} : Finset Bool) else Finset.univ)
      (fun _ b => if b then p else 1 - p)
  have hfac : ∀ x : Fin n,
      (∑ c ∈ (if x ∈ W then ({false} : Finset Bool) else Finset.univ),
        (if c then p else 1 - p)) = if x ∈ W then 1 - p else 1 := by
    intro x
    by_cases hx : x ∈ W
    · simp [hx]
    · simp [hx]
  simp only [hfac] at h
  have hfilter : (Finset.univ.filter (fun x : Fin n => x ∈ W)) = W := by
    ext x; simp
  have hprod : (∏ x : Fin n, if x ∈ W then 1 - p else 1) = (1 - p) ^ W.card := by
    rw [← Finset.prod_filter, hfilter, Finset.prod_const]
  rw [hprod] at h
  simpa [Prob, wt, badSet] using h.symm
