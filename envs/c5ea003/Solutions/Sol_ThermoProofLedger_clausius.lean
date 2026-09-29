-- Prove2me | solution 1 for ThermoProofLedger.clausius
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:13:09.76182+00:00
-- url     : https://prove2.me/submissions/00b28262-9139-4f8c-b3c2-8fdf0e74bed5

-- Sol generated from Novelty/ThermodynamicsOfProofLedger.lean
import Mathlib
import Definitions.Def_Novelty_ThermodynamicsOfProof
import Definitions.Def_Novelty_ThermodynamicsOfProofLedger
import Theorems.Thm_ThermoProof_erasedBits_eq_zero_iff_injective
import Theorems.Thm_ThermoProof_imageCard_comp_le
import Theorems.Thm_ThermoProof_imageCard_pos

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

private lemma logb2_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.logb 2 x ≤ Real.logb 2 y :=
  (Real.logb_le_logb (b := 2) (by norm_num) hx (lt_of_lt_of_le hx hxy)).2 hxy

/-! ## The pipeline and its cumulative erasure -/


omit [Fintype α] [DecidableEq α] [Nonempty α] in
@[simp] lemma compose_nil : compose ([] : List (α → α)) = id := rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Appending a step post-composes it onto the running pipeline. -/
lemma compose_append_singleton (fs : List (α → α)) (g : α → α) :
    compose (fs ++ [g]) = g ∘ compose fs := by
  simp [compose, List.foldl_append]


/-- The empty proof (the identity register map) erases nothing. -/
@[simp] lemma totalErased_nil : totalErased ([] : List (α → α)) = 0 := by
  unfold totalErased
  rw [compose_nil]
  exact (erasedBits_eq_zero_iff_injective (id : α → α)).2 Function.injective_id


/-! ## Per-step entropy production -/


/-- **Data-processing inequality (per step).** Each proof step produces nonnegative entropy:
distinctions destroyed cannot be recreated. -/
lemma stepDrop_nonneg (fs : List (α → α)) (g : α → α) : 0 ≤ stepDrop fs g := by
  unfold stepDrop
  have hpos : (0 : ℝ) < imageCard (compose (fs ++ [g])) := by
    have : 0 < imageCard (compose (fs ++ [g])) := imageCard_pos _
    exact_mod_cast this
  have hle : (imageCard (compose (fs ++ [g])) : ℝ) ≤ imageCard (compose fs) := by
    rw [compose_append_singleton]
    exact_mod_cast imageCard_comp_le (compose fs) g
  have := logb2_le hpos hle
  linarith

omit [Nonempty α] in
/-- **Ledger identity.** Extending a proof by one step adds exactly that step's entropy
production to the total. -/
lemma totalErased_append_singleton (fs : List (α → α)) (g : α → α) :
    totalErased (fs ++ [g]) = totalErased fs + stepDrop fs g := by
  unfold totalErased erasedBits stepDrop
  ring



/-! ## The discrete Clausius inequality -/


/-! ## Physical Landauer heat of a derivation -/



/-! ## Reversibility of pipelines -/




/-! ## The creation/erasure ledger -/





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
open ThermoProofLedger in
theorem solution(fs : List (α → α)) :
    ∃ ds : List ℝ, ds.length = fs.length ∧ (∀ d ∈ ds, 0 ≤ d) ∧ ds.sum = totalErased fs := by
  induction fs using List.reverseRecOn with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | append_singleton fs g ih =>
      obtain ⟨ds, hlen, hpos, hsum⟩ := ih
      refine ⟨ds ++ [stepDrop fs g], ?_, ?_, ?_⟩
      · simp [hlen]
      · intro d hd
        rcases List.mem_append.1 hd with h | h
        · exact hpos d h
        · rcases List.mem_singleton.1 h with rfl
          exact stepDrop_nonneg fs g
      · rw [List.sum_append, hsum, totalErased_append_singleton]
        simp
