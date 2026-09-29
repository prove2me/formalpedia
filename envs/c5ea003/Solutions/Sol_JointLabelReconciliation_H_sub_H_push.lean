-- Prove2me | solution 1 for JointLabelReconciliation.H_sub_H_push
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:21:51.76464+00:00
-- url     : https://prove2.me/submissions/6a17817e-d2fc-425e-a3b5-672b9a7a179a

-- Sol generated from Applications/JointLabelReconciliation.lean
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




/-! ## Strictness on the audited `4 × 9` population -/
















open JointLabelReconciliation in
theorem solution(f : α → α') (p : α → ℝ) :
    H univ p - H univ (push f p) = ∑ u : α', D (fib f u) p := by
  have h1 : ∑ u : α', H (fib f u) p = H univ p := by
    simpa [H, fib] using Finset.sum_fiberwise (univ : Finset α) f (fun x => nlp (p x))
  have h2 : H univ (push f p) = ∑ u : α', nlp (∑ x ∈ fib f u, p x) := rfl
  rw [h2, ← h1, ← Finset.sum_sub_distrib]
  rfl
