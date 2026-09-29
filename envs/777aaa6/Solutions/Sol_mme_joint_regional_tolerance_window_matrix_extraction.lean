-- Prove2me | solution 1 for mme_joint_regional_tolerance_window_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T12:41:50.692985+00:00
-- url     : https://prove2.me/submissions/5d1ddb14-733e-4a15-be9b-32d880790ecc

import Theorems.Thm_mme_logarithmic_joint_regional_recipe_compilation
import Theorems.Thm_mme_joint_regional_CW_plan_sound
import Definitions.Def_mme_logarithmic_joint_regional_CW_recipe
import Theorems.Thm_mme_regional_tolerance_window_step_family

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.RecursiveYZ.CWCells
open MME.TensorObj
set_option autoImplicit false

/-- A tolerance-window family supplies one region of a joint logarithmic stage. -/
theorem mme_regional_tolerance_window_log_part_stage
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (delta eps rate : ℝ) (hdelta : 0 ≤ delta) (heps : 0 < eps) (hrate : 0 ≤ rate)
    (hsize : (8 * D.repairScale : ℝ) *
      (25 * D.R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        (D.minimum : ℝ) * eps^2)
    (hbudget : ∀ mu : WindowProfile D, WindowAdmissible D mu →
      (∀ i, WindowClose D delta i (mu i)) → rate ≤ windowLogBudget D mu eps) :
    ∃ E : LogPartStage M ell (parentWindow D (eps + 2 * delta)) (childWindow D delta),
      E.types ≤ (Fintype.card (Position D.n) + 1) ^
        (3 * Fintype.card (Cell D.half D.R D.parent) * Fintype.card (CompleteWord ell)) ∧
      E.rate = rate := by
  obtain ⟨types, steps, htypes, hbudget, inside, cover⟩ :=
    mme_regional_tolerance_window_step_family D delta eps rate hdelta heps hsize hbudget
  exact ⟨.step types rate hrate steps hbudget inside cover, htypes, rfl⟩

/-- Regional tolerance windows compose simultaneously around a shared lower-level recipe.
The input losses multiply, while the logarithmic output budgets add. -/
theorem mme_joint_regional_tolerance_window_log_recipe_descent
    {N ell upper parts : ℕ} {P Q : Predicate N}
    (hlevel : ell < upper) (size : Fin parts → ℕ)
    (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (base : ∀ j, Predicate (size j)) (D : ∀ j, IntegerStep ell (size j) (base j))
    (delta eps rate : Fin parts → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j) (heps : ∀ j, 0 < eps j) (hrate : ∀ j, 0 ≤ rate j)
    (hsize : ∀ j, (8 * (D j).repairScale : ℝ) *
      (25 * (D j).R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        ((D j).minimum : ℝ) * (eps j)^2)
    (hbudget : ∀ j (mu : WindowProfile (D j)), WindowAdmissible (D j) mu →
      (∀ i, WindowClose (D j) (delta j) i (mu i)) →
        rate j ≤ windowLogBudget (D j) mu (eps j))
    (source : ∀ i x, (∀ j, parentWindow (D j) (eps j + 2 * delta j) i
      (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
    (target : ∀ i x, Q i x → ∀ j, childWindow (D j) (delta j) i
      (fun r ↦ x (positions ⟨j,r⟩)))
    (next : LogJointRecipe N ell Q) :
    ∃ E : LogJointRecipe N upper P,
      E.inputs ≤ (∏ j, (Fintype.card (Position (D j).n) + 1) ^
        (3 * Fintype.card (Cell (D j).half (D j).R (D j).parent) *
          Fintype.card (CompleteWord ell))) * next.inputs ∧
      E.logOutputs = (∑ j, rate j) + next.logOutputs ∧ E.dims = next.dims := by
  classical
  have hpart (j : Fin parts) := mme_regional_tolerance_window_log_part_stage
    (D j) (delta j) (eps j) (rate j) (hdelta j) (heps j) (hrate j) (hsize j) (hbudget j)
  choose steps htypes hrates using hpart
  refine ⟨.stage hlevel size positions
    (fun j ↦ parentWindow (D j) (eps j + 2 * delta j))
    (fun j ↦ childWindow (D j) (delta j)) source steps target next, ?_, ?_, rfl⟩
  · exact Nat.mul_le_mul_right next.inputs (Finset.prod_le_prod' fun j _ ↦ htypes j)
  · change (∑ j, (steps j).rate) + next.logOutputs = _
    simp only [hrates]

#print axioms mme_regional_tolerance_window_log_part_stage
#print axioms mme_joint_regional_tolerance_window_log_recipe_descent

universe u

/-- Joint window descent yields an actual matrix direct-sum restriction. -/
theorem solution
    {K : Type u} [Field K] {N ell upper parts : ℕ} {P Q : Predicate N}
    (hlevel : ell < upper) (size : Fin parts → ℕ)
    (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (base : ∀ j, Predicate (size j)) (D : ∀ j, IntegerStep ell (size j) (base j))
    (delta eps rate : Fin parts → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j) (heps : ∀ j, 0 < eps j) (hrate : ∀ j, 0 ≤ rate j)
    (hsize : ∀ j, (8 * (D j).repairScale : ℝ) *
      (25 * (D j).R * (Fintype.card (CompleteWord ell) : ℝ)^2) ≤
        ((D j).minimum : ℝ) * (eps j)^2)
    (hbudget : ∀ j (mu : WindowProfile (D j)), WindowAdmissible (D j) mu →
      (∀ i, WindowClose (D j) (delta j) i (mu i)) →
        rate j ≤ windowLogBudget (D j) mu (eps j))
    (source : ∀ i x, (∀ j, parentWindow (D j) (eps j + 2 * delta j) i
      (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
    (target : ∀ i x, Q i x → ∀ j, childWindow (D j) (delta j) i
      (fun r ↦ x (positions ⟨j,r⟩)))
    (next : LogJointRecipe N ell Q) :
    ∃ inputs copies : ℕ,
      inputs ≤ (∏ j, (Fintype.card (Position (D j).n) + 1) ^
        (3 * Fintype.card (Cell (D j).half (D j).R (D j).parent) *
          Fintype.card (CompleteWord ell))) * next.inputs ∧
      Real.exp ((∑ j, rate j) + next.logOutputs) ≤ (copies : ℝ) ∧
      TensorObj.Restrict
        (bigAdd (fun _ : Fin copies ↦ MMObj K next.a next.b next.c))
        (bigAdd (fun _ : Fin inputs ↦ tensor K P)) := by
  obtain ⟨E, hi, ho, hd⟩ := mme_joint_regional_tolerance_window_log_recipe_descent
    hlevel size positions base D delta eps rate hdelta heps hrate hsize hbudget
      source target next
  obtain ⟨A, hai, hao, had⟩ := mme_logarithmic_joint_regional_recipe_compilation E
  refine ⟨A.inputs, A.outputs, hai.trans_le hi, ?_, ?_⟩
  · simpa only [ho] using hao
  · simpa only [JointPlan.a, JointPlan.b, JointPlan.c, had, hd,
      LogJointRecipe.a, LogJointRecipe.b, LogJointRecipe.c] using
      (mme_joint_regional_CW_plan_sound A (K := K))

#print axioms solution
