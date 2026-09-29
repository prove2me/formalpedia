-- Prove2me | Definitions.Def_Tropical_CompressionDelta_Core
-- name    : Tropical_CompressionDelta_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:49.007053+00:00
-- url     : https://prove2.me/theorems/13d154f3-6285-4fe3-be23-7f146767bf14
-- title:
--   Aether Catalog definitions — Tropical_CompressionDelta_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.CompressionDelta.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/CompressionDelta/Core.lean by skeleton subtraction
import Mathlib

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

namespace CompressionDelta

variable {M : Type*}

/-! ## Infimum helpers over `ℕ` -/




/-! ## Schedules and their cost -/

/-- `scheduleCost dlt prev cs ms` is the total number of bits transmitted when the decoder
starts in state `prev`, the stream of messages has residual-cost functions `cs`, and the
encoder decides to put the decoder in state `ms.get i` for the `i`-th message.  Each step
pays the model delta `dlt` for the switch and then the residual for the message.

Schedules shorter than the message stream are meaningless; the definition returns the cost
of the common prefix, and every theorem below quantifies over schedules of the correct
length. -/
def scheduleCost (dlt : M → M → ℕ) : M → List (M → ℕ) → List M → ℕ
  | _, [], _ => 0
  | _, _ :: _, [] => 0
  | prev, c :: cs, m :: ms => dlt prev m + c m + scheduleCost dlt m cs ms



/-- The min-plus dynamic program: the least number of bits an adaptive protocol can
transmit for the stream `cs`, starting from decoder state `prev`. -/
noncomputable def optCost [Finite M] [Nonempty M] (dlt : M → M → ℕ) :
    M → List (M → ℕ) → ℕ
  | _, [] => 0
  | prev, c :: cs => ⨅ m : M, (dlt prev m + c m + optCost dlt m cs)

variable [Finite M] [Nonempty M]



/-! ## Bellman optimality -/




/-! ## The amortized upper bound: pay the delta once -/


/-! ## The matching lower bound: the rate is a hard floor -/


end CompressionDelta


