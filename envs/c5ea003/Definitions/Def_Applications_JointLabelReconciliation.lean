-- Prove2me | Definitions.Def_Applications_JointLabelReconciliation
-- name    : Applications_JointLabelReconciliation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:43.612438+00:00
-- url     : https://prove2.me/theorems/a6d5b032-0470-4626-b58c-0e336df86508
-- title:
--   Aether Catalog definitions — Applications_JointLabelReconciliation
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.JointLabelReconciliation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/JointLabelReconciliation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ChainedLabelWidth
import Definitions.Def_Applications_LabelEntropyDeficit
/-
# The joint-label reconciliation: encoding-invariance and one-sided artifacts

## Context (FACT round-29 #2, verdict "THE-ORIGINAL-STANDS")

Two runs on an *identical* population disagreed about the joint channel:
a width-valid chained encoding reported `36` labels and a large mutual
information, a rebuild using a too-narrow decimal frame reported `18` labels
and a much smaller mutual information.  Which reading is the artifact?

This file answers the question *structurally*, i.e. without access to either
run's data:

* `MI_pushFst_eq_of_injective` — **encoding invariance**: any two width-valid
  (injective) label encodings of the same population give the *same* mutual
  information.  Two clean re-implementations therefore *must* agree; agreement
  is evidence of correctness, and paper 91's value is reproduced by the clean
  cross-check for this reason.
* `MI_pushFst_le` — **one-sidedness (data-processing inequality)**: a
  non-injective label encoding can only *lower* the measured mutual
  information.  Collision artifacts are therefore *signed*: the discrepant
  reading is always the smaller one, so the larger of two readings on the same
  population is the admissible one.
* `narrow_frame_strictly_loses` — on the audited `4 × 9` population the narrow
  `·3` frame strictly loses label entropy, quantitatively:
  `H(narrow labels) ≤ log₂ 36 - 1/18`.

Together: a disagreement between a width-valid and a width-invalid chaining can
only be resolved *in favour of the width-valid one*.  This is the formal content
of the verdict.

The entropy toolkit lives in `Applications.LabelEntropyDeficit`, the arithmetic
of chained frames in `Applications.ChainedLabelWidth`.
-/

namespace JointLabelReconciliation

open Finset LabelEntropy

variable {α β α' : Type*} [Fintype α] [Fintype β] [Fintype α'] [DecidableEq α']

/-- The fiber of a labelling map `f` over the label `u`. -/
def fib (f : α → α') (u : α') : Finset α := {x ∈ (univ : Finset α) | f x = u}


/-- Pushforward of a weight function along a labelling. -/
noncomputable def push (f : α → α') (p : α → ℝ) : α' → ℝ := fun u => ∑ x ∈ fib f u, p x

/-- Pushforward of a *joint* weight function along a labelling of the first
coordinate (the second coordinate is the reference variable). -/
noncomputable def pushFst (f : α → α') (p : α × β → ℝ) : α' × β → ℝ :=
  fun q => ∑ x ∈ fib f q.1, p (x, q.2)

/-- First marginal. -/
noncomputable def marg1 (p : α × β → ℝ) : α → ℝ := fun x => ∑ y : β, p (x, y)

/-- Second marginal. -/
noncomputable def marg2 (p : α × β → ℝ) : β → ℝ := fun y => ∑ x : α, p (x, y)

/-- Mutual information (bits) of a joint weight function. -/
noncomputable def MI (p : α × β → ℝ) : ℝ :=
  H univ (marg1 p) + H univ (marg2 p) - H univ p

/-! ## Entropy loss of a labelling equals the total fiber deficit -/





/-! ## Marginals of a coarsened joint weight -/




/-! ## The two structural theorems -/




/-! ## Strictness on the audited `4 × 9` population -/


section Audited

/-- The audited population: `4 × 9 = 36` code pairs. -/
abbrev Pop : Type := Fin 4 × Fin 9

/-- A width-valid chaining of the audited population (frame `9 ≥ 9`). -/
def encWide (q : Pop) : Fin 40 := ⟨9 * (q.1 : ℕ) + (q.2 : ℕ), by have := q.1.isLt; have := q.2.isLt; omega⟩

/-- The rebuild's narrow chaining of the same population (frame `3 < 9`). -/
def encNarrow (q : Pop) : Fin 40 := ⟨3 * (q.1 : ℕ) + (q.2 : ℕ), by have := q.1.isLt; have := q.2.isLt; omega⟩

/-- The uniform population weight. -/
noncomputable def unif : Pop → ℝ := fun _ => 1 / 36








end Audited

end JointLabelReconciliation


