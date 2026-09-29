-- Prove2me | Theorems.Thm_CompressionDelta_rate_mul_length_le_optCost
-- name    : CompressionDelta.rate_mul_length_le_optCost
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:34:51.26826+00:00
-- url     : https://prove2.me/theorems/4ac99da9-8715-4ff9-97f7-acb32f996e91
-- title:
--   The residual rate is a floor.
-- statement:
--   **The residual rate is a floor.**  If every message costs at least `r` bits in every
--   decoder state, then no adaptive protocol transmits fewer than `r` bits per message,
--   whatever it does with the model delta.
--
--   ```lean
--   theorem CompressionDelta.rate_mul_length_le_optCost(dlt : M → M → ℕ) (r : ℕ) :
--       ∀ (cs : List (M → ℕ)), (∀ c ∈ cs, ∀ m : M, r ≤ c m) → ∀ prev : M,
--         cs.length * r ≤ optCost dlt prev cs := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/CompressionDelta/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/CompressionDelta/Core.lean#L168

-- Thm stub generated from Tropical/CompressionDelta/Core.lean
import Mathlib
import Definitions.Def_Tropical_CompressionDelta_Core

/-!
# Amortized model-delta compression, I: the min-plus (tropical) core

This file is part of the research thread *Compression Beyond the Pigeonhole Bound*,
Phase A / Question 1: **separating the decompressor from the data**.

## Modelling decision

A streaming compression protocol with a *shared, adaptable decompressor* is described by
two nonnegative integer cost functions (all costs are in bits):

* a family of **residual costs** `c : M → ℕ`, one function per message in the stream,
  where `c m` is the number of bits needed to code that message when the decoder is in
  model state `m`;
* a **model-delta cost** `dlt : M → M → ℕ`, where `dlt m m'` is the number of bits that
  must be transmitted to move the shared decoder from state `m` to state `m'`
  (a LoRA-style patch, a codebook index, a dictionary, …).

The total number of transmitted bits for a *schedule* (a choice of decoder state for each
message) is the alternating sum of deltas and residuals; the protocol optimum is the
minimum over schedules.  Both operations — "add costs along a path", "take the minimum
over paths" — are exactly multiplication and addition in the **min-plus (tropical)
semiring**, which is why this development lives in the Tropical catalog.  The tropical
semiring bridge itself is `CompressionDelta.TropicalBridge`.

## Main results

* `CompressionDelta.optCost_le_scheduleCost` — the DP value is a lower bound for every
  schedule of the right length.
* `CompressionDelta.exists_schedule_scheduleCost_eq` — the DP value is attained.
* `CompressionDelta.isLeast_optCost` — hence the DP value *is* the protocol optimum
  (Bellman optimality for the model-switching problem).
* `CompressionDelta.optCost_le_stay` — the "pay the delta once, then never switch"
  upper bound; this is the amortized protocol.
* `CompressionDelta.rate_mul_length_le_optCost` — no protocol can beat the per-message
  residual rate: the delta can only ever be amortized *down to* the rate, never below it.
-/

open CompressionDelta

variable {M : Type*}

/-! ## Infimum helpers over `ℕ` -/




/-! ## Schedules and their cost -/





variable [Finite M] [Nonempty M]



/-! ## Bellman optimality -/




/-! ## The amortized upper bound: pay the delta once -/


/-! ## The matching lower bound: the rate is a hard floor -/

theorem CompressionDelta.rate_mul_length_le_optCost(dlt : M → M → ℕ) (r : ℕ) :
    ∀ (cs : List (M → ℕ)), (∀ c ∈ cs, ∀ m : M, r ≤ c m) → ∀ prev : M,
      cs.length * r ≤ optCost dlt prev cs := by sorry
