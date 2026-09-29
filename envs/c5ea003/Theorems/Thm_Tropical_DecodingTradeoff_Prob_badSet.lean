-- Prove2me | Theorems.Thm_Tropical_DecodingTradeoff_Prob_badSet
-- name    : Tropical.DecodingTradeoff.Prob_badSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:33.58448+00:00
-- url     : https://prove2.me/theorems/ad4e228d-3f14-41c3-a8cf-cebd7aab1b61
-- title:
--   Exact cylinder probability.
-- statement:
--   **Exact cylinder probability.**  An uninformative set of `c` positions has probability
--   exactly `(1 - p) ^ c`.
--
--   ```lean
--   theorem Tropical.DecodingTradeoff.Prob_badSet(p : ℝ) {n : ℕ} (W : Finset (Fin n)) :
--       Prob p (badSet n W) = (1 - p) ^ W.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/DecodingTradeoff/Environment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/DecodingTradeoff/Environment.lean#L127

-- Thm stub generated from Tropical/DecodingTradeoff/Environment.lean
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

theorem Tropical.DecodingTradeoff.Prob_badSet(p : ℝ) {n : ℕ} (W : Finset (Fin n)) :
    Prob p (badSet n W) = (1 - p) ^ W.card := by sorry
