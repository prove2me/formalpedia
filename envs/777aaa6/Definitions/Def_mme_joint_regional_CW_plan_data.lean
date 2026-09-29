-- Prove2me | Definitions.Def_mme_joint_regional_CW_plan_data
-- name    : mme_joint_regional_CW_plan_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T00:48:30.669606+00:00
-- url     : https://prove2.me/theorems/52201757-7a18-4bb2-981c-65059a3189a3
-- title:
--   Joint regional CW plans: oriented part stages with a joint continuation
-- statement:
--   A part stage is one exact-type hashing step on the positions of one part, in any of the six mode orientations. A joint regional plan extends a regional plan by a joint regional stage: the positions are split into parts, each part takes its own part stage, and a single continuation plan runs on all positions of the product of the parts' outputs, as in More Asymmetry Theorem 6.4 and Algorithm 1.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_recursive_regional_CW_data

open BigOperators MME MME.TensorObj
set_option autoImplicit false

namespace MME.ProfiledCW

/-- One exact-type hashing step on the positions of a single part, carrying the
part's source predicate `S` to its target predicate `T`, in any of the six mode
orientations (via `rotate`/`swap`). -/
inductive PartStage : (M lower : ℕ) → Predicate M → Predicate M → Type
  | step {M lower : ℕ} {S T : Predicate M} (types copies : ℕ)
      (steps : Fin types → ExactStep lower M S)
      (enough : ∀ j, copies ≤ (steps j).copies)
      (inside : ∀ j i x, (steps j).output i x → T i x)
      (cover : ∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
        ∃! j, ∀ i, (steps j).output i (x i)) : PartStage M lower S T
  | rotate {M lower : ℕ} {S T : Predicate M} (child : PartStage M lower S T) :
      PartStage M lower (fun i ↦ S (cyclicPerm.symm i)) (fun i ↦ T (cyclicPerm.symm i))
  | swap {M lower : ℕ} {S T : Predicate M} (child : PartStage M lower S T) :
      PartStage M lower (fun i ↦ S (swapFirstTwoPerm.symm i)) (fun i ↦ T (swapFirstTwoPerm.symm i))

def PartStage.types {M lower : ℕ} {S T : Predicate M} : PartStage M lower S T → ℕ
  | .step types _ _ _ _ _ => types
  | .rotate D => D.types
  | .swap D => D.types

def PartStage.copies {M lower : ℕ} {S T : Predicate M} : PartStage M lower S T → ℕ
  | .step _ copies _ _ _ _ => copies
  | .rotate D => D.copies
  | .swap D => D.copies

/-- `RegionalPlan` extended by a **joint regional stage**: the positions are split into
parts, each part takes its own hashing step (with its own orientation), and a single
continuation runs on all positions of the product of the parts' outputs. This is the
shape of More Asymmetry, Theorem 6.4 and Algorithm 1: every stage acts on the whole
interface tensor produced by the previous one. -/
inductive JointPlan : (N ell : ℕ) → Predicate N → Type
  | base {N ell P} (data : RegionalPlan N ell P) : JointPlan N ell P
  | stage {N ell lower parts : ℕ} {P Q : Predicate N}
      (level_decreases : lower < ell)
      (size : Fin parts → ℕ)
      (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (S T : ∀ j, Predicate (size j))
      (source : ∀ i x, (∀ j, S j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (steps : ∀ j, PartStage (size j) lower (S j) (T j))
      (target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j,r⟩)))
      (next : JointPlan N lower Q) : JointPlan N ell P
  | partition {N ell parts : ℕ} {P : Predicate N}
      (size : Fin parts → ℕ)
      (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
      (Q : ∀ j, Predicate (size j))
      (inside : ∀ i x, (∀ j, Q j i (fun r ↦ x (positions ⟨j,r⟩))) → P i x)
      (children : ∀ j, JointPlan (size j) ell (Q j)) : JointPlan N ell P
  | rotate {N ell P} (child : JointPlan N ell P) :
      JointPlan N ell (fun i ↦ P (cyclicPerm.symm i))
  | swap {N ell P} (child : JointPlan N ell P) :
      JointPlan N ell (fun i ↦ P (swapFirstTwoPerm.symm i))

def JointPlan.inputs {N ell : ℕ} {P : Predicate N} : JointPlan N ell P → ℕ
  | .base D => D.inputs
  | .stage _ _ _ _ _ _ steps _ next => (∏ j, (steps j).types) * next.inputs
  | .partition _ _ _ _ children => ∏ j, (children j).inputs
  | .rotate D => D.inputs
  | .swap D => D.inputs

def JointPlan.outputs {N ell : ℕ} {P : Predicate N} : JointPlan N ell P → ℕ
  | .base D => D.outputs
  | .stage _ _ _ _ _ _ steps _ next => (∏ j, (steps j).copies) * next.outputs
  | .partition _ _ _ _ children => ∏ j, (children j).outputs
  | .rotate D => D.outputs
  | .swap D => D.outputs

def JointPlan.dims {N ell : ℕ} {P : Predicate N} : JointPlan N ell P → ℕ × ℕ × ℕ
  | .base D => D.dims
  | .stage _ _ _ _ _ _ _ _ next => next.dims
  | .partition _ _ _ _ children =>
      (∏ j, (children j).dims.1, ∏ j, (children j).dims.2.1, ∏ j, (children j).dims.2.2)
  | .rotate D => (D.dims.2.2, D.dims.1, D.dims.2.1)
  | .swap D => (D.dims.2.2, D.dims.2.1, D.dims.1)

def JointPlan.a {N ell : ℕ} {P : Predicate N} (D : JointPlan N ell P) : ℕ := D.dims.1
def JointPlan.b {N ell : ℕ} {P : Predicate N} (D : JointPlan N ell P) : ℕ := D.dims.2.1
def JointPlan.c {N ell : ℕ} {P : Predicate N} (D : JointPlan N ell P) : ℕ := D.dims.2.2

end MME.ProfiledCW


