-- Prove2me | Theorems.Thm_CompressionDelta_optCost_le_stay
-- name    : CompressionDelta.optCost_le_stay
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:34:32.155295+00:00
-- url     : https://prove2.me/theorems/613a1ea3-9b1a-4e11-869e-30d71457fe7a
-- title:
--   Pay the delta once.
-- statement:
--   **Pay the delta once.**  If staying in a model is free (`dlt m m = 0`), the protocol
--   that switches to `m` for the first message and never switches again transmits
--   `dlt prev m` bits of model delta plus the residuals; hence the optimum is at most that.
--
--   ```lean
--   theorem CompressionDelta.optCost_le_stay(dlt : M → M → ℕ) (hself : ∀ m : M, dlt m m = 0) (m : M) :
--       ∀ (cs : List (M → ℕ)) (prev : M),
--         optCost dlt prev cs ≤ dlt prev m + (cs.map (fun c => c m)).sum := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/CompressionDelta/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/CompressionDelta/Core.lean#L148

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

theorem CompressionDelta.optCost_le_stay(dlt : M → M → ℕ) (hself : ∀ m : M, dlt m m = 0) (m : M) :
    ∀ (cs : List (M → ℕ)) (prev : M),
      optCost dlt prev cs ≤ dlt prev m + (cs.map (fun c => c m)).sum := by sorry
