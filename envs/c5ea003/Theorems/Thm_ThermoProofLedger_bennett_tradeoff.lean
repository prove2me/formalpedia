-- Prove2me | Theorems.Thm_ThermoProofLedger_bennett_tradeoff
-- name    : ThermoProofLedger.bennett_tradeoff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:39:45.436264+00:00
-- url     : https://prove2.me/theorems/f350c7ed-de2f-43cc-80ac-3236c8729392
-- title:
--   The Bennett creation/erasure trade-off.
-- statement:
--   **The Bennett creation/erasure trade-off.** For any step `f : α → β`, Bennett's reversible
--   dilation `x ↦ (x, f x)` erases *zero* bits, but pays for its reversibility by *creating*
--   exactly `log₂(card β)` bits of ancilla register.  Thus erasure and creation are the two sides
--   of a single ledger: logical irreversibility can always be traded for allocation.
--
--   ```lean
--   theorem ThermoProofLedger.bennett_tradeoff{β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] (f : α → β) :
--       erasedBits (bennettEmbedding f) = 0 ∧
--         createdBits (Fintype.card α) (Fintype.card (α × β)) = Real.logb 2 (Fintype.card β) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ThermodynamicsOfProofLedger.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ThermodynamicsOfProofLedger.lean#L202

-- Thm stub generated from Novelty/ThermodynamicsOfProofLedger.lean
import Mathlib
import Definitions.Def_Novelty_ThermodynamicsOfProof
import Definitions.Def_Novelty_ThermodynamicsOfProofLedger

/-!
# Thermodynamics of Mathematical Proof — the Clausius/second-law ledger

This file extends the single-step erasure theory of `ThermodynamicsOfProof` from an isolated
proof step `f : α → β` to an entire **proof pipeline**: a finite list of steps
`fs = [f₁, f₂, …, f_k]` all operating on a fixed finite register `α`, applied in temporal
order.  We track the *cumulative* information erased along the derivation and establish a
discrete **second law of proof thermodynamics**.

The composite of the pipeline is `compose fs = f_k ∘ … ∘ f₂ ∘ f₁`, and the total information
erased is `totalErased fs = erasedBits (compose fs)`.

## Main results

* `totalErased_append_singleton` — appending a step adds exactly its incremental entropy
  production `stepDrop`.
* `stepDrop_nonneg` — every step produces a nonnegative amount of entropy (data processing).
* `totalErased_mono_prefix` — **monotonicity of a proof pipeline**: extending a derivation can
  only increase the total dissipated entropy; erasure is never undone downstream.
* `clausius` — **discrete Clausius inequality**: the total erasure of a pipeline decomposes as
  a sum of nonnegative per-step entropy productions, one per inference.
* `totalHeat_mono_prefix` — the physical Landauer heat of a derivation is monotone in the
  length of the derivation.
* `reversible_iff_totalErased_zero` — a pipeline is logically reversible (its composite is
  injective) iff it dissipates zero entropy.
* `totalErased_zero_of_forall_injective` — a pipeline built entirely from reversible steps is
  free.
* `createdBits` and `bennett_tradeoff` — the **creation/erasure ledger**: Bennett's reversible
  dilation `x ↦ (x, f x)` erases nothing but instead *creates* exactly `log₂(card β)` bits of
  ancilla — the thermodynamic trade-off between erasure and allocation.
-/

open Finset Real ThermoProof

open ThermoProofLedger

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ## A monotonicity helper for base-2 logarithm -/


/-! ## The pipeline and its cumulative erasure -/







/-! ## Per-step entropy production -/






/-! ## The discrete Clausius inequality -/


/-! ## Physical Landauer heat of a derivation -/



/-! ## Reversibility of pipelines -/




/-! ## The creation/erasure ledger -/

theorem ThermoProofLedger.bennett_tradeoff{β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] (f : α → β) :
    erasedBits (bennettEmbedding f) = 0 ∧
      createdBits (Fintype.card α) (Fintype.card (α × β)) = Real.logb 2 (Fintype.card β) := by sorry
