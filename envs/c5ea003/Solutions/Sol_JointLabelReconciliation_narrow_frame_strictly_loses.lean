-- Prove2me | solution 1 for JointLabelReconciliation.narrow_frame_strictly_loses
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:04:22.870949+00:00
-- url     : https://prove2.me/submissions/7969ede5-04bc-4424-8b57-93966fd4e8a8

-- Sol generated from Applications/JointLabelReconciliation.lean
import Mathlib
import Definitions.Def_Applications_ChainedLabelWidth
import Definitions.Def_Applications_JointLabelReconciliation
import Definitions.Def_Applications_LabelEntropyDeficit
import Theorems.Thm_JointLabelReconciliation_H_sub_H_push
import Theorems.Thm_LabelEntropy_D_eq
import Theorems.Thm_LabelEntropy_D_nonneg
import Theorems.Thm_LabelEntropy_D_pos_of_two_positive
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

/-- The quantitative loss of a labelling: the deficit of a single fiber already
bounds the entropy drop. -/
theorem H_push_le_of_fiber (f : α → α') (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (u : α') :
    H univ (push f p) ≤ H univ p - D (fib f u) p := by
  have h := H_sub_H_push f p
  have hrest : D (fib f u) p ≤ ∑ v : α', D (fib f v) p := by
    refine Finset.single_le_sum (f := fun v => D (fib f v) p) ?_ (Finset.mem_univ u)
    exact fun v _ => D_nonneg fun x _ => hp x
  linarith








/-- Uniform label entropy of the audited population is `log₂ 36` bits. -/
theorem entropy_unif : H (univ : Finset Pop) unif = Real.logb 2 36 := by
  have hcard : (Finset.univ : Finset Pop).card = 36 := by decide
  have hterm : ∀ q : Pop, nlp (unif q) = (1 / 36) * Real.logb 2 36 := by
    intro q
    have hlog : Real.logb 2 ((1:ℝ)/36) = - Real.logb 2 36 := by
      rw [one_div, Real.logb_inv]
    simp only [nlp, unif, hlog]
    ring
  rw [H, Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const, hcard, nsmul_eq_mul]
  push_cast
  ring

/-- The `·3` frame merges the pairs `(0,3)` and `(1,0)`: both live in the fiber
over the label `3`. -/
lemma fiber_three_has_two :
    ((0 : Fin 4), (3 : Fin 9)) ∈ fib encNarrow ⟨3, by omega⟩ ∧
      ((1 : Fin 4), (0 : Fin 9)) ∈ fib encNarrow ⟨3, by omega⟩ := by
  constructor <;> decide






open JointLabelReconciliation in
theorem solution:
    H (univ : Finset (Fin 40)) (push encNarrow unif) ≤ Real.logb 2 36 - 1 / 18 := by
  have hnn : ∀ q : Pop, (0:ℝ) ≤ unif q := fun _ => by norm_num [unif]
  obtain ⟨hi, hj⟩ := fiber_three_has_two
  have hpos : (0:ℝ) < D (fib encNarrow ⟨3, by omega⟩) unif := by
    refine D_pos_of_two_positive (fun x _ => hnn x) hi hj (by decide) ?_ ?_ <;>
      norm_num [unif]
  -- quantitative form: the two merged atoms alone cost `2 · (1/36) · log₂ 2`
  have hbound : (1:ℝ)/18 ≤ D (fib encNarrow ⟨3, by omega⟩) unif := by
    classical
    rw [D_eq]
    set S := ∑ k ∈ fib encNarrow (⟨3, by omega⟩ : Fin 40), unif k with hS
    have hSge : (2:ℝ)/36 ≤ S := by
      have hpair : ((0 : Fin 4), (3 : Fin 9)) ≠ ((1 : Fin 4), (0 : Fin 9)) := by decide
      have : ∑ k ∈ ({((0 : Fin 4), (3 : Fin 9)), ((1 : Fin 4), (0 : Fin 9))} : Finset Pop),
          unif k ≤ S := by
        rw [hS]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hnn k)
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> assumption
      rw [Finset.sum_pair hpair] at this
      have hval : unif ((0 : Fin 4), (3 : Fin 9)) + unif ((1 : Fin 4), (0 : Fin 9))
          = (2:ℝ)/36 := by norm_num [unif]
      linarith [hval ▸ this]
    have hterms : ∀ k ∈ fib encNarrow (⟨3, by omega⟩ : Fin 40),
        (1/36 : ℝ) * (Real.logb 2 2) ≤ unif k * (Real.logb 2 S - Real.logb 2 (unif k)) := by
      intro k _
      have h1 : Real.logb 2 ((1:ℝ)/18) ≤ Real.logb 2 S :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith [hSge])
      have h2 : Real.logb 2 ((1:ℝ)/18) - Real.logb 2 ((1:ℝ)/36) = Real.logb 2 2 := by
        rw [show (1:ℝ)/18 = 2 * (1/36) by norm_num, Real.logb_mul (by norm_num) (by norm_num)]
        ring
      have : Real.logb 2 2 ≤ Real.logb 2 S - Real.logb 2 (unif k) := by
        simp only [unif]
        linarith
      calc (1/36 : ℝ) * Real.logb 2 2 ≤ (1/36 : ℝ) * (Real.logb 2 S - Real.logb 2 (unif k)) := by
            exact mul_le_mul_of_nonneg_left this (by norm_num)
        _ = unif k * (Real.logb 2 S - Real.logb 2 (unif k)) := by simp [unif]
    have hcard2 : 2 ≤ (fib encNarrow (⟨3, by omega⟩ : Fin 40)).card := by decide
    have hsum := Finset.sum_le_sum hterms
    rw [Finset.sum_const, Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at hsum
    have : (2:ℝ) * (1/36) ≤ (fib encNarrow (⟨3, by omega⟩ : Fin 40)).card * ((1/36 : ℝ) * 1) := by
      have : (2:ℝ) ≤ ((fib encNarrow (⟨3, by omega⟩ : Fin 40)).card : ℝ) := by
        exact_mod_cast hcard2
      nlinarith
    simp only [nsmul_eq_mul] at hsum
    linarith
  have hle := H_push_le_of_fiber encNarrow unif hnn (⟨3, by omega⟩ : Fin 40)
  rw [entropy_unif] at hle
  linarith
