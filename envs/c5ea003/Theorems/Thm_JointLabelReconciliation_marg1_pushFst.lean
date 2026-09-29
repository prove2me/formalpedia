-- Prove2me | Theorems.Thm_JointLabelReconciliation_marg1_pushFst
-- name    : JointLabelReconciliation.marg1_pushFst
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:54:50.38245+00:00
-- url     : https://prove2.me/theorems/fb4ba982-f72b-4f6a-b499-97762bdbdb88
-- title:
--   Marg1 pushFst
-- statement:
--   Formal statement of `JointLabelReconciliation.marg1_pushFst` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem JointLabelReconciliation.marg1_pushFst(f : α → α') (p : α × β → ℝ) :
--       marg1 (pushFst f p) = push f (marg1 p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/JointLabelReconciliation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/JointLabelReconciliation.lean#L115

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

omit [Fintype α'] in

theorem JointLabelReconciliation.marg1_pushFst(f : α → α') (p : α × β → ℝ) :
    marg1 (pushFst f p) = push f (marg1 p) := by sorry
