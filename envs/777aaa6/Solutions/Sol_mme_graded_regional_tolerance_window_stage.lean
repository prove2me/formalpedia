-- Prove2me | solution 1 for mme_graded_regional_tolerance_window_stage
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:49:02.231307+00:00
-- url     : https://prove2.me/submissions/6f88b61c-67c9-487f-8827-e1298b70eaba

import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_regional_tolerance_window_data
import Theorems.Thm_mme_regional_parent_mixture_lipschitz
import Theorems.Thm_mme_regional_supported_histogram_admissibility
import Theorems.Thm_mme_prescribed_histogram_polynomial_type_cover
import Theorems.Thm_mme_regional_target_marginals

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-!
The profile enumeration and ordinary-step construction follow raresbuhai's
accepted proof of `mme_regional_tolerance_window_step_family`, submission
08deb303-0e4b-483f-828c-b099e373d0d8. Keeping the structural fields literal lets
the same family act on a graded source. The new source hypothesis uses parent
grades only; it does not assert the existence of a target-histogram address.
-/

theorem solution
    {ell M : ℕ} {P S : Predicate M} (D : IntegerStep ell M P)
    (delta eps rate : ℝ) (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ) ^ 2) ≤
        (D.minimum : ℝ) * eps ^ 2)
    (hsource : ∀ i x,
      ParentGraded D.parent D.n i (split D.positions D.length x) →
      parentWindow D (eps + 2 * delta) i x → S i x)
    (hbudget : ∀ mu : WindowProfile D, WindowAdmissible D mu →
      (∀ i, WindowClose D delta i (mu i)) →
        rate ≤ windowLogBudget D mu eps) :
    ∃ E : LogPartStageG M ell S (childWindow D delta),
      E.rate = rate ∧
      E.types ≤ (Fintype.card (Position D.n) + 1) ^
        (3 * Fintype.card (Cell D.half D.R D.parent) *
          Fintype.card (CompleteWord ell)) ∧
      ((∃ x : Fin 3 → FineWord M,
        supported x ∧ ∀ i, childWindow D delta i (x i)) → 1 ≤ E.types) := by
  classical
  let supportedWords (x : Fin 3 → Position D.n → CompleteWord ell) : Prop :=
    ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2
  obtain ⟨types, profiles, typeBound, witnesses, insideWindow, coverWindow⟩ :=
    mme_prescribed_histogram_polynomial_type_cover (fullCell D.total D.reference)
      supportedWords (fun i f ↦ Graded D.total i D.reference f) (WindowClose D delta)
  have admissible (j : Fin types) : WindowAdmissible D (profiles j) := by
    obtain ⟨x, supportedTriple, profileData⟩ := witnesses j
    have profileEq : (fun i ↦ count (fullCell D.total D.reference) (x i)) = profiles j :=
      funext fun i ↦ funext fun c ↦ funext fun w ↦ (profileData i).2.2 c w
    have constraints := mme_regional_supported_histogram_admissibility D x
      (fun i ↦ (profileData i).1) supportedTriple
    change WindowAdmissible D
      (fun i ↦ count (fullCell D.total D.reference) (x i)) at constraints
    rwa [profileEq] at constraints
  have closeProfiles (j : Fin types) : ∀ i, WindowClose D delta i (profiles j i) := by
    obtain ⟨x, supportedTriple, profileData⟩ := witnesses j
    exact fun i ↦ (profileData i).2.1
  have splitMass :=
    (mme_regional_target_marginals D.m 0 D.reference D.reference_target).1
  let ordinarySteps (j : Fin types) :
      IntegerStep ell M (parentWindow D (eps + 2 * delta)) := {
    half := D.half
    R := D.R
    parent := D.parent
    n := D.n
    total := D.total
    half_eq := D.half_eq
    m := D.m
    N := D.N
    hashPositions := D.hashPositions
    L := D.L
    positions := D.positions
    length := D.length
    mu := profiles j
    mass := (admissible j).1
    support := (admissible j).2.1
    boundary := (admissible j).2.2
    reference := D.reference
    reference_target := D.reference_target
    minimum := D.minimum
    repairScale := D.repairScale
    minimum_pos := D.minimum_pos
    repairScale_gt_one := D.repairScale_gt_one
    parent_size := D.parent_size
    split_divisible := D.split_divisible
    epsilon := eps
    epsilon_pos := heps
    size_test := hsize
    source_inside := fun i x hx ↦
      (mme_regional_parent_mixture_lipschitz D.total D.n D.m splitMass
        (profiles j i) (D.mu i) delta hdelta (closeProfiles j i)).2 eps
          (split D.positions D.length x) hx }
  let gradedSteps (j : Fin types) : IntegerStepG ell M S := {
    B := parentWindow D (eps + 2 * delta)
    step := ordinarySteps j
    graded_inside := fun i x parentGrades inWindow ↦ hsource i x parentGrades inWindow }
  have budget (j : Fin types) : rate ≤ (gradedSteps j).step.certifiedLogCopies :=
    hbudget (profiles j) (admissible j) (closeProfiles j)
  have inside : ∀ j i x, (gradedSteps j).step.output i x → childWindow D delta i x := by
    intro j i x hx
    exact insideWindow j i (split D.positions D.length x) hx
  have cover : ∀ x : Fin 3 → FineWord M,
      supported x → (∀ i, childWindow D delta i (x i)) →
        ∃! j, ∀ i, (gradedSteps j).step.output i (x i) := by
    intro x supportedTriple inWindow
    exact coverWindow (fun i ↦ split D.positions D.length (x i))
      (fun p r ↦ supportedTriple
        (Fin.cast D.length (finProdFinEquiv (D.positions.symm p, r)))) inWindow
  let stage := LogPartStageG.step types rate hrate gradedSteps budget inside cover
  refine ⟨stage, rfl, typeBound, ?_⟩
  rintro ⟨x, supportedTriple, inWindow⟩
  obtain ⟨j, _, _⟩ := cover x supportedTriple inWindow
  change 1 ≤ types
  have indexBound := j.isLt
  omega

#print axioms solution
