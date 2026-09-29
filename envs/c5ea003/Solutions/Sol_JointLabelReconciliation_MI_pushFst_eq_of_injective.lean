-- Prove2me | solution 1 for JointLabelReconciliation.MI_pushFst_eq_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:27:18.022056+00:00
-- url     : https://prove2.me/submissions/dc0070a5-015b-4e00-87b0-a3f8569c897e

-- Sol generated from Applications/JointLabelReconciliation.lean
import Mathlib
import Definitions.Def_Applications_ChainedLabelWidth
import Definitions.Def_Applications_JointLabelReconciliation
import Definitions.Def_Applications_LabelEntropyDeficit
import Theorems.Thm_JointLabelReconciliation_H_joint_sub
import Theorems.Thm_JointLabelReconciliation_H_sub_H_push
import Theorems.Thm_JointLabelReconciliation_marg1_pushFst
import Theorems.Thm_JointLabelReconciliation_marg2_pushFst
import Theorems.Thm_LabelEntropy_nlp_zero
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


omit [Fintype α'] in
@[simp] lemma mem_fib {f : α → α'} {u : α'} {x : α} : x ∈ fib f u ↔ f x = u := by
  simp [fib]






/-! ## Entropy loss of a labelling equals the total fiber deficit -/



omit [Fintype α'] in
/-- Fibers of an injective labelling carry no deficit. -/
lemma D_fib_eq_zero_of_injective {f : α → α'} (hf : Function.Injective f) (u : α')
    (p : α → ℝ) : D (fib f u) p = 0 := by
  classical
  rcases Finset.eq_empty_or_nonempty (fib f u) with hE | ⟨x, hx⟩
  · simp [D, H, hE]
  · have hsingle : fib f u = {x} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, fun z hz => ?_⟩
      have h1 : f z = u := mem_fib.mp hz
      have h2 : f x = u := mem_fib.mp hx
      exact hf (h1.trans h2.symm)
    simp [D, H, hsingle]

/-- **Encoding invariance for entropy**: an injective relabelling preserves
label entropy exactly. -/
theorem H_push_eq_of_injective {f : α → α'} (hf : Function.Injective f) (p : α → ℝ) :
    H univ (push f p) = H univ p := by
  have h := H_sub_H_push f p
  rw [Finset.sum_congr rfl (fun u _ => D_fib_eq_zero_of_injective hf u p)] at h
  simp only [Finset.sum_const_zero] at h
  linarith

/-! ## Marginals of a coarsened joint weight -/




/-! ## The two structural theorems -/




/-! ## Strictness on the audited `4 × 9` population -/
















open JointLabelReconciliation in
theorem solution{f : α → α'} (hf : Function.Injective f)
    (p : α × β → ℝ) : MI (pushFst f p) = MI p := by
  have h1 : H univ (marg1 (pushFst f p)) = H univ (marg1 p) := by
    rw [marg1_pushFst, H_push_eq_of_injective hf]
  have h2 : H univ (marg2 (pushFst f p)) = H univ (marg2 p) := by
    rw [marg2_pushFst]
  have h3 : H univ (pushFst f p) = H univ p := by
    have h := H_joint_sub f p
    have hz : ∑ u : α', ∑ y : β, D (fib f u) (fun x => p (x, y)) = 0 :=
      Finset.sum_eq_zero fun u _ =>
        Finset.sum_eq_zero fun y _ => D_fib_eq_zero_of_injective hf u _
    rw [hz] at h
    linarith
  simp only [MI, h1, h2, h3]
