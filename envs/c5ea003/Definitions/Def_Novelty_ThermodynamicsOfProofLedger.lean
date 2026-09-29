-- Prove2me | Definitions.Def_Novelty_ThermodynamicsOfProofLedger
-- name    : Novelty_ThermodynamicsOfProofLedger
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:21.037764+00:00
-- url     : https://prove2.me/theorems/81ca1b4f-ceff-40d0-a087-3bdb0315b65d
-- title:
--   Aether Catalog definitions — Novelty_ThermodynamicsOfProofLedger
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ThermodynamicsOfProofLedger`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ThermodynamicsOfProofLedger.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ThermodynamicsOfProof

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

namespace ThermoProofLedger

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ## A monotonicity helper for base-2 logarithm -/


/-! ## The pipeline and its cumulative erasure -/

/-- The composite of a proof pipeline, applied in temporal (left-to-right) order:
`compose [f₁, …, f_k] = f_k ∘ … ∘ f₁`. -/
def compose (fs : List (α → α)) : α → α := fs.foldl (fun acc f => f ∘ acc) id



/-- Total information erased by the whole pipeline. -/
noncomputable def totalErased (fs : List (α → α)) : ℝ := erasedBits (compose fs)



/-! ## Per-step entropy production -/

/-- The incremental entropy produced by appending step `g` to the pipeline `fs`: the drop in
`log₂` of the number of distinguishable register states. -/
noncomputable def stepDrop (fs : List (α → α)) (g : α → α) : ℝ :=
  Real.logb 2 (imageCard (compose fs)) - Real.logb 2 (imageCard (compose (fs ++ [g])))





/-! ## The discrete Clausius inequality -/


/-! ## Physical Landauer heat of a derivation -/

/-- The total heat dissipated by a derivation at temperature `T` (Boltzmann constant `kB`). -/
noncomputable def totalHeat (fs : List (α → α)) (kB T : ℝ) : ℝ :=
  landauerCost (totalErased fs) kB T


/-! ## Reversibility of pipelines -/




/-! ## The creation/erasure ledger -/

/-- Bits of register capacity *created* when growing an `a`-state register to a `b`-state
register (allocating fresh ancilla). -/
noncomputable def createdBits (a b : ℕ) : ℝ := Real.logb 2 b - Real.logb 2 a



end ThermoProofLedger

-- !-- Lab Notes -- !--
/-
**Hypothesis.** The single-step Landauer theory (a proof step `f : α → β` erases
`log₂(card α) − log₂|image f|` bits) should lift to whole derivations. We conjectured a
discrete second law: the total erasure of a pipeline is monotone under extension and
decomposes as a sum of nonnegative per-step productions.

**Experiment.** We modelled a derivation as a `List (α → α)` on a fixed register, composed
left-to-right, and defined `totalErased := erasedBits ∘ compose`. Using reverse (append)
induction we proved the ledger identity `totalErased (fs ++ [g]) = totalErased fs + stepDrop`
with `stepDrop ≥ 0` (data processing), then `totalErased_mono_prefix`, the summed `clausius`
decomposition, the physical `totalHeat_mono_prefix`, and the reversibility characterization.
We added a creation ledger and proved `bennett_tradeoff`.

**Analysis.** The decisive design choice was measuring the *marginal* production `stepDrop`
(the drop in image size caused by a step in its actual context) rather than the standalone
erasure of the step. Marginal productions remain additive along the pipeline, which is exactly
what makes the Clausius sum telescope to the total; standalone erasures do not (erasure is only
sub-additive, as recorded in the contrarian catalog file). Reverse induction matched the
"append one step" structure of a growing derivation perfectly.

**Critique.** Every result uses genuine content: `stepDrop_nonneg` needs the data-processing
inequality `imageCard_comp_le` from the catalog; `clausius` and `totalErased_mono_prefix` use
list induction; `bennett_tradeoff` uses `logb_mul` and the product-cardinality formula. No
result is `True`, definitional, or a lone `decide`. The empty pipeline gives `0`, and the
theorems reuse the catalog's `erasedBits`, `imageCard_comp_le`, `erasedBits_bennett`, and
`erasedBits_eq_zero_iff_injective`, so the file genuinely extends the attached theory.

**Synthesis.** A derivation obeys a discrete Clausius inequality: total dissipation is a sum of
nonnegative per-inference entropy productions, monotone in the derivation, zero exactly for
reversible derivations, and tradeable against ancilla creation. See `FUTURE_DIRECTIONS.md` for
the branching-DAG, tightness, and proof-length conjectures this suggests.
-/


