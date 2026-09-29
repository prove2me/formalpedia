-- Prove2me | Definitions.Def_mme_logarithmic_joint_regional_CW_recipe
-- name    : mme_logarithmic_joint_regional_CW_recipe
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T00:49:18.462729+00:00
-- url     : https://prove2.me/theorems/d16c24c2-87c2-4def-9f0d-b7552943821d
-- title:
--   Logarithmic joint regional CW recipes
-- statement:
--   A logarithmic part stage uses integer steps on one part with a common certified logarithmic copy budget, in any orientation. A logarithmic joint recipe extends a logarithmic regional recipe by joint regional stages whose logarithmic output is the sum of the part budgets plus that of the continuation.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_logarithmic_regional_CW_recipe

open BigOperators MME MME.ProfiledCW
set_option autoImplicit false

namespace MME.RegionRealization

/-- One part of a joint regional stage at the logarithmic level: integer steps on the
part's positions with a common certified logarithmic copy budget, in any orientation. -/
inductive LogPartStage : (M lower : ℕ) → Predicate M → Predicate M → Type
  | step {M lower : ℕ} {S T : Predicate M} (types : ℕ) (rate : ℝ) (rate_nonneg : 0 ≤ rate)
      (steps : Fin types → IntegerStep lower M S)
      (budget : ∀ j, rate ≤ (steps j).certifiedLogCopies)
      (inside : ∀ j i x, (steps j).output i x → T i x)
      (cover : ∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i)) : LogPartStage M lower S T
  | rotate {M lower : ℕ} {S T : Predicate M} (child : LogPartStage M lower S T) :
      LogPartStage M lower (fun i ↦ S (cyclicPerm.symm i)) (fun i ↦ T (cyclicPerm.symm i))
  | swap {M lower : ℕ} {S T : Predicate M} (child : LogPartStage M lower S T) :
      LogPartStage M lower (fun i ↦ S (swapFirstTwoPerm.symm i))
        (fun i ↦ T (swapFirstTwoPerm.symm i))

def LogPartStage.types {M lower : ℕ} {S T : Predicate M} : LogPartStage M lower S T → ℕ
  | .step types _ _ _ _ _ _ => types
  | .rotate D => D.types
  | .swap D => D.types

def LogPartStage.rate {M lower : ℕ} {S T : Predicate M} : LogPartStage M lower S T → ℝ
  | .step _ rate _ _ _ _ _ => rate
  | .rotate D => D.rate
  | .swap D => D.rate

/-- A logarithmic recipe with joint regional stages; every existing `LogRecipe` is a base. -/
inductive LogJointRecipe : (N ell : ℕ) → Predicate N → Type
  | base {N ell P} (data : LogRecipe N ell P) : LogJointRecipe N ell P
  | stage {N ell lower parts : ℕ} {P Q : Predicate N}
      (level_decreases : lower < ell)
      (size : Fin parts → ℕ)
      (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (S T : ∀ j, Predicate (size j))
      (source : ∀ i x, (∀ j, S j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (steps : ∀ j, LogPartStage (size j) lower (S j) (T j))
      (target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j,r⟩)))
      (next : LogJointRecipe N lower Q) : LogJointRecipe N ell P
  | partition {N ell parts : ℕ} {P : Predicate N}
      (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (Q : ∀ j, Predicate (size j))
      (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (children : ∀ j, LogJointRecipe (size j) ell (Q j)) : LogJointRecipe N ell P
  | rotate {N ell P} (child : LogJointRecipe N ell P) :
      LogJointRecipe N ell (fun i ↦ P (cyclicPerm.symm i))
  | swap {N ell P} (child : LogJointRecipe N ell P) :
      LogJointRecipe N ell (fun i ↦ P (swapFirstTwoPerm.symm i))

def LogJointRecipe.inputs {N ell : ℕ} {P : Predicate N} : LogJointRecipe N ell P → ℕ
  | .base D => D.inputs
  | .stage _ _ _ _ _ _ steps _ next => (∏ j, (steps j).types) * next.inputs
  | .partition _ _ _ _ children => ∏ j, (children j).inputs
  | .rotate D => D.inputs
  | .swap D => D.inputs

noncomputable def LogJointRecipe.logOutputs {N ell : ℕ} {P : Predicate N} :
    LogJointRecipe N ell P → ℝ
  | .base D => D.logOutputs
  | .stage _ _ _ _ _ _ steps _ next => (∑ j, (steps j).rate) + next.logOutputs
  | .partition _ _ _ _ children => ∑ j, (children j).logOutputs
  | .rotate D => D.logOutputs
  | .swap D => D.logOutputs

def LogJointRecipe.dims {N ell : ℕ} {P : Predicate N} : LogJointRecipe N ell P → ℕ × ℕ × ℕ
  | .base D => D.dims
  | .stage _ _ _ _ _ _ _ _ next => next.dims
  | .partition _ _ _ _ children =>
      (∏ j, (children j).dims.1, ∏ j, (children j).dims.2.1, ∏ j, (children j).dims.2.2)
  | .rotate D => (D.dims.2.2, D.dims.1, D.dims.2.1)
  | .swap D => (D.dims.2.2, D.dims.2.1, D.dims.1)

def LogJointRecipe.a {N ell : ℕ} {P : Predicate N} (D : LogJointRecipe N ell P) : ℕ := D.dims.1
def LogJointRecipe.b {N ell : ℕ} {P : Predicate N} (D : LogJointRecipe N ell P) : ℕ := D.dims.2.1
def LogJointRecipe.c {N ell : ℕ} {P : Predicate N} (D : LogJointRecipe N ell P) : ℕ := D.dims.2.2

end MME.RegionRealization


