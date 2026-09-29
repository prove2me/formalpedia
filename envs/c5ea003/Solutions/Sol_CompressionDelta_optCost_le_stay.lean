-- Prove2me | solution 1 for CompressionDelta.optCost_le_stay
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:48:32.229873+00:00
-- url     : https://prove2.me/submissions/8e19f032-488c-492a-b6c2-eb145163525a

-- Sol generated from Tropical/CompressionDelta/Core.lean
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

/-- The infimum of a family of naturals indexed by a nonempty type is a lower bound. -/
theorem natInf_le {ι : Type*} [Nonempty ι] (f : ι → ℕ) (i : ι) : (⨅ j, f j) ≤ f i :=
  ciInf_le (OrderBot.bddBelow _) i



/-! ## Schedules and their cost -/





variable [Finite M] [Nonempty M]

@[simp] theorem optCost_nil (dlt : M → M → ℕ) (prev : M) : optCost dlt prev [] = 0 := by
  rw [optCost]

theorem optCost_cons (dlt : M → M → ℕ) (prev : M) (c : M → ℕ) (cs : List (M → ℕ)) :
    optCost dlt prev (c :: cs) = ⨅ m : M, (dlt prev m + c m + optCost dlt m cs) := by
  rw [optCost]

/-! ## Bellman optimality -/




/-! ## The amortized upper bound: pay the delta once -/


/-! ## The matching lower bound: the rate is a hard floor -/



open CompressionDelta in
theorem solution(dlt : M → M → ℕ) (hself : ∀ m : M, dlt m m = 0) (m : M) :
    ∀ (cs : List (M → ℕ)) (prev : M),
      optCost dlt prev cs ≤ dlt prev m + (cs.map (fun c => c m)).sum := by
  intro cs
  induction cs with
  | nil => intro prev; simp
  | cons c cs ih =>
      intro prev
      rw [optCost_cons]
      refine le_trans (natInf_le _ m) ?_
      have h := ih m
      rw [hself m] at h
      simp only [List.map_cons, List.sum_cons]
      omega
