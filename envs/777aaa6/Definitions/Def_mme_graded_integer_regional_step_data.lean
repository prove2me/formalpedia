-- Prove2me | Definitions.Def_mme_graded_integer_regional_step_data
-- name    : mme_graded_integer_regional_step_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T15:38:26.348151+00:00
-- url     : https://prove2.me/theorems/99cd2e8f-ea35-448d-a8e9-757f1b42bb0d
-- title:
--   Graded-source integer regional steps and graded joint recipes
-- statement:
--   Parent-graded words (in every parent occurrence the halves' grades add up to the parent's grade); graded-source integer steps (an integer step over a band predicate whose parent-graded words lie in the actual source); logarithmic part stages and logarithmic joint regional recipes built from them.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: interface tensors fix the level structure exactly and let only complete-split distributions vary (Definitions 3.6 and 4.1); Theorem 6.4, Section 6.6 and Algorithm 1 chain the stages. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_logarithmic_regional_CW_recipe

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.ProfiledCW
set_option autoImplicit false

namespace MME.RegionRealization

/-- Every parent occurrence carries its parent type's grade in mode `i`: the two halves' grades
add up to the parent's coordinate. -/
def ParentGraded {R ell : ℕ} (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ) (i : Fin 3)
    (f : Position n → CompleteSplit.CompleteWord ell) : Prop :=
  ∀ r (t : Fin (n r)), CWCells.grade (f ⟨r, t, 0⟩) + CWCells.grade (f ⟨r, t, 1⟩) = parent r i

/-- An integer step whose actual source `P` need only contain the **parent-graded** words of its
typical band: `step` is an ordinary integer step over the band predicate `B`, and every
parent-graded `B`-word lies in `P`. -/
structure IntegerStepG (ell M : ℕ) (P : ProfiledCW.Predicate M) where
  B : ProfiledCW.Predicate M
  step : IntegerStep ell M B
  graded_inside : ∀ i x, ParentGraded step.parent step.n i
    (ProfiledCW.split step.positions step.length x) → B i x → P i x

/-- One part of a joint regional stage with graded-source integer steps. -/
inductive LogPartStageG : (M lower : ℕ) → Predicate M → Predicate M → Type
  | step {M lower : ℕ} {S T : Predicate M} (types : ℕ) (rate : ℝ) (rate_nonneg : 0 ≤ rate)
      (steps : Fin types → IntegerStepG lower M S)
      (budget : ∀ j, rate ≤ (steps j).step.certifiedLogCopies)
      (inside : ∀ j i x, (steps j).step.output i x → T i x)
      (cover : ∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
        ∃! j, ∀ i, (steps j).step.output i (x i)) : LogPartStageG M lower S T
  | rotate {M lower : ℕ} {S T : Predicate M} (child : LogPartStageG M lower S T) :
      LogPartStageG M lower (fun i ↦ S (cyclicPerm.symm i)) (fun i ↦ T (cyclicPerm.symm i))
  | swap {M lower : ℕ} {S T : Predicate M} (child : LogPartStageG M lower S T) :
      LogPartStageG M lower (fun i ↦ S (swapFirstTwoPerm.symm i))
        (fun i ↦ T (swapFirstTwoPerm.symm i))

def LogPartStageG.types {M lower : ℕ} {S T : Predicate M} : LogPartStageG M lower S T → ℕ
  | .step types _ _ _ _ _ _ => types
  | .rotate D => D.types
  | .swap D => D.types

def LogPartStageG.rate {M lower : ℕ} {S T : Predicate M} : LogPartStageG M lower S T → ℝ
  | .step _ rate _ _ _ _ _ => rate
  | .rotate D => D.rate
  | .swap D => D.rate

/-- A logarithmic joint recipe whose stages use graded-source integer steps. -/
inductive LogJointRecipeG : (N ell : ℕ) → Predicate N → Type
  | base {N ell P} (data : LogRecipe N ell P) : LogJointRecipeG N ell P
  | stage {N ell lower parts : ℕ} {P Q : Predicate N}
      (level_decreases : lower < ell)
      (size : Fin parts → ℕ)
      (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (S T : ∀ j, Predicate (size j))
      (source : ∀ i x, (∀ j, S j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (steps : ∀ j, LogPartStageG (size j) lower (S j) (T j))
      (target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j,r⟩)))
      (next : LogJointRecipeG N lower Q) : LogJointRecipeG N ell P
  | partition {N ell parts : ℕ} {P : Predicate N}
      (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (Q : ∀ j, Predicate (size j))
      (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (children : ∀ j, LogJointRecipeG (size j) ell (Q j)) : LogJointRecipeG N ell P
  | rotate {N ell P} (child : LogJointRecipeG N ell P) :
      LogJointRecipeG N ell (fun i ↦ P (cyclicPerm.symm i))
  | swap {N ell P} (child : LogJointRecipeG N ell P) :
      LogJointRecipeG N ell (fun i ↦ P (swapFirstTwoPerm.symm i))

def LogJointRecipeG.inputs {N ell : ℕ} {P : Predicate N} : LogJointRecipeG N ell P → ℕ
  | .base D => D.inputs
  | .stage _ _ _ _ _ _ steps _ next => (∏ j, (steps j).types) * next.inputs
  | .partition _ _ _ _ children => ∏ j, (children j).inputs
  | .rotate D => D.inputs
  | .swap D => D.inputs

noncomputable def LogJointRecipeG.logOutputs {N ell : ℕ} {P : Predicate N} :
    LogJointRecipeG N ell P → ℝ
  | .base D => D.logOutputs
  | .stage _ _ _ _ _ _ steps _ next => (∑ j, (steps j).rate) + next.logOutputs
  | .partition _ _ _ _ children => ∑ j, (children j).logOutputs
  | .rotate D => D.logOutputs
  | .swap D => D.logOutputs

def LogJointRecipeG.dims {N ell : ℕ} {P : Predicate N} : LogJointRecipeG N ell P → ℕ × ℕ × ℕ
  | .base D => D.dims
  | .stage _ _ _ _ _ _ _ _ next => next.dims
  | .partition _ _ _ _ children =>
      (∏ j, (children j).dims.1, ∏ j, (children j).dims.2.1, ∏ j, (children j).dims.2.2)
  | .rotate D => (D.dims.2.2, D.dims.1, D.dims.2.1)
  | .swap D => (D.dims.2.2, D.dims.2.1, D.dims.1)

def LogJointRecipeG.a {N ell : ℕ} {P : Predicate N} (D : LogJointRecipeG N ell P) : ℕ := D.dims.1
def LogJointRecipeG.b {N ell : ℕ} {P : Predicate N} (D : LogJointRecipeG N ell P) : ℕ := D.dims.2.1
def LogJointRecipeG.c {N ell : ℕ} {P : Predicate N} (D : LogJointRecipeG N ell P) : ℕ := D.dims.2.2

end MME.RegionRealization


