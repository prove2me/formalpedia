-- Prove2me | Theorems.Thm_Tropical_DecodingTradeoff_mem_badSet
-- name    : Tropical.DecodingTradeoff.mem_badSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:29.865141+00:00
-- url     : https://prove2.me/theorems/756aa4df-8385-4930-8fd8-c84a4405cde7
-- title:
--   Mem badSet
-- statement:
--   Formal statement of `Tropical.DecodingTradeoff.mem_badSet` from the Aether Catalog (Tropical). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Tropical.DecodingTradeoff.mem_badSet{n : ℕ} {W : Finset (Fin n)} (ω : Fin n → Bool) :
--       ω ∈ badSet n W ↔ ∀ x ∈ W, ω x = false := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/DecodingTradeoff/Environment.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/DecodingTradeoff/Environment.lean#L113

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

theorem Tropical.DecodingTradeoff.mem_badSet{n : ℕ} {W : Finset (Fin n)} (ω : Fin n → Bool) :
    ω ∈ badSet n W ↔ ∀ x ∈ W, ω x = false := by sorry
