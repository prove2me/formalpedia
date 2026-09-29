-- Prove2me | Theorems.Thm_JointLabelReconciliation_MI_pushFst_le
-- name    : JointLabelReconciliation.MI_pushFst_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:55:43.692358+00:00
-- url     : https://prove2.me/theorems/df854e85-c4e9-4d58-962c-5fad28e89e21
-- title:
--   Data-processing inequality for label coarsenings.
-- statement:
--   **Data-processing inequality for label coarsenings.**  An arbitrary (in
--   particular a collision-producing) label encoding can only *decrease* the
--   measured mutual information.  Collision artifacts are therefore one-sided.
--
--   ```lean
--   theorem JointLabelReconciliation.MI_pushFst_le{f : α → α'} {p : α × β → ℝ} (hp : ∀ q, 0 ≤ p q) :
--       MI (pushFst f p) ≤ MI p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/JointLabelReconciliation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/JointLabelReconciliation.lean#L173

-- Thm stub generated from Applications/JointLabelReconciliation.lean
import Mathlib
import Definitions.Def_Applications_ChainedLabelWidth
import Definitions.Def_Applications_JointLabelReconciliation
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

open JointLabelReconciliation

open Finset LabelEntropy

variable {α β α' : Type*} [Fintype α] [Fintype β] [Fintype α'] [DecidableEq α']








/-! ## Entropy loss of a labelling equals the total fiber deficit -/





/-! ## Marginals of a coarsened joint weight -/




/-! ## The two structural theorems -/

theorem JointLabelReconciliation.MI_pushFst_le{f : α → α'} {p : α × β → ℝ} (hp : ∀ q, 0 ≤ p q) :
    MI (pushFst f p) ≤ MI p := by sorry
