-- Prove2me | solution 1 for mme_graded_integer_step_low_level_log_recipe
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T04:03:16.016545+00:00
-- url     : https://prove2.me/submissions/9ace1703-9c50-4c39-9c1a-51f8f046e2b6

import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_regional_tolerance_window_data
import Theorems.Thm_mme_integer_step_low_level_boundary_end

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
  MME.RegionRealization
set_option autoImplicit false

/- The terminal boundary profiles are supplied by Robertboy18's accepted
   elementary-depth boundary theorem, p2m:theorem/bd0aea3a-f65f-45e6-bba2-7d13ce9492ad.
   This assembly retains the graded-source step instead of requiring an ordinary
   source inclusion. The parent-window specialization follows the tolerance
   replacement in p2m:theorem/4623db12-9558-436a-9820-c0990c34485e. -/
namespace GradedTermination

private def singlePositions (M : ℕ) : ((j : Fin 1) × Fin M) ≃ Fin M where
  toFun := fun p => p.2
  invFun := fun p => ⟨0, p⟩
  left_inv := by
    rintro ⟨j, p⟩
    have hj : j = 0 := Subsingleton.elim j 0
    subst j
    rfl
  right_inv := fun _ => rfl

private theorem terminal_recipe
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStepG ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.step.total D.step.reference))
    (rate : ℝ) (hrate : 0 ≤ rate) (hbudget : rate ≤ D.step.certifiedLogCopies) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.step.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogJointRecipeG M upper P,
        E.inputs = 1 ∧ E.logOutputs = rate ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by
  obtain ⟨z, profiles, hshape, hprofile, boundary, _, ha, hb, hc⟩ :=
    mme_integer_step_low_level_boundary_end D.step hlevel part
  let extraction : LogPartStageG M ell P D.step.output :=
    .step 1 rate hrate (fun _ => D) (fun _ => hbudget)
      (fun _ _ _ hx => hx)
      (fun _ _ hx => ⟨0, hx, fun j _ => Subsingleton.elim j 0⟩)
  let E : LogJointRecipeG M upper P :=
    .stage (parts := 1) (Q := D.step.output) hupper
      (fun _ => M) (singlePositions M)
      (fun _ => P) (fun _ => D.step.output)
      (fun _ _ hx => hx 0) (fun _ => extraction)
      (fun _ _ hx _ => hx) (.base (.boundary boundary))
  refine ⟨z, profiles, hshape, hprofile, E, ?_, ?_, ?_⟩
  · simp [E, extraction, LogJointRecipeG.inputs, LogPartStageG.types, LogRecipe.inputs]
  · simp [E, extraction, LogJointRecipeG.logOutputs, LogPartStageG.rate,
      LogRecipe.logOutputs]
  · change (boundary.a, boundary.b, boundary.c) = _
    rw [ha, hb, hc]

/-- The central budget terminates a parent-graded parent window, without requiring
    ordinary ungraded band words to satisfy the actual source. -/
theorem parent_window_recipe
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.total D.reference))
    (eps eta rate : ℝ) (heps : 0 < eps) (heta : eps ≤ eta)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ) ^ 2) ≤
        (D.minimum : ℝ) * eps ^ 2)
    (hbudget : rate ≤ windowLogBudget D D.mu eps) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogJointRecipeG M upper
        (fun i x => ParentGraded D.parent D.n i (split D.positions D.length x) ∧
          parentWindow D eta i x),
        E.inputs = 1 ∧ E.logOutputs = rate ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by
  let bandStep : IntegerStep ell M (parentWindow D eta) := {
    D with
    epsilon := eps
    epsilon_pos := heps
    size_test := hsize
    source_inside := by
      intro i x hx r w
      exact (hx r w).trans_le heta }
  let gradedStep : IntegerStepG ell M
      (fun i x => ParentGraded D.parent D.n i (split D.positions D.length x) ∧
        parentWindow D eta i x) := {
    B := parentWindow D eta
    step := bandStep
    graded_inside := fun _ _ hgrade hband => ⟨hgrade, hband⟩ }
  have budget : rate ≤ gradedStep.step.certifiedLogCopies := hbudget
  exact terminal_recipe gradedStep hlevel hupper part rate hrate budget

end GradedTermination

theorem solution
    {ell M upper : ℕ} {P : Predicate M} (D : IntegerStepG ell M P)
    (hlevel : ell ≤ 1) (hupper : ell < upper)
    (part : Partition (fullCell D.step.total D.step.reference))
    (rate : ℝ) (hrate : 0 ≤ rate) (hbudget : rate ≤ D.step.certifiedLogCopies) :
    ∃ (z : Fin part.parts → Fin 3)
      (profiles : ∀ j, Boundary.Profile ell (part.size j)),
      (∀ j i, ((part.cells j).2.val i).val = (profiles j).shape (z j) i) ∧
      (∀ j i, D.step.mu i (part.cells j) = (profiles j).mu (z j) i) ∧
      ∃ E : LogJointRecipeG M upper P,
        E.inputs = 1 ∧ E.logOutputs = rate ∧
        E.dims = (∏ j, (profiles j).a (z j),
          ∏ j, (profiles j).b (z j), ∏ j, (profiles j).c (z j)) := by
  exact GradedTermination.terminal_recipe D hlevel hupper part rate hrate hbudget

#print axioms GradedTermination.parent_window_recipe
#print axioms solution
