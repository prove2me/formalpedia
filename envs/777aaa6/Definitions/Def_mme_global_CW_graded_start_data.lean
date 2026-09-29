-- Prove2me | Definitions.Def_mme_global_CW_graded_start_data
-- name    : mme_global_CW_graded_start_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T15:39:54.407899+00:00
-- url     : https://prove2.me/theorems/4002300c-bb1c-49e3-809b-d36575573129
-- title:
--   Global CW start with a graded joint continuation
-- statement:
--   An unpaired global extraction split into oriented parts, followed by a graded logarithmic joint regional recipe on its whole interface; inputs, logarithmic outputs and matrix dimensions.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: interface tensors fix the level structure exactly and let only complete-split distributions vary (Definitions 3.6 and 4.1); Theorem 6.4, Section 6.6 and Algorithm 1 chain the stages. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_global_CW_joint_start_data
import Definitions.Def_mme_graded_integer_regional_step_data

open BigOperators MME MME.ProfiledCW
set_option autoImplicit false

namespace MME.GlobalCW

/-- A genuine unpaired global extraction followed by a **graded** joint regional recipe on its
whole interface. -/
structure StartG (M ell : ℕ) where
  parts : ℕ
  size : Fin parts → ℕ
  positions : ((j : Fin parts) × Fin (size j)) ≃ Fin M
  T : ∀ j, Predicate (size j)
  steps : ∀ j, Part (size j) ell (T j)
  Q : Predicate M
  target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j,r⟩))
  next : RegionRealization.LogJointRecipeG M ell Q

def StartG.inputs {M ell : ℕ} (D : StartG M ell) : ℕ :=
  (∏ j, (D.steps j).inputs) * D.next.inputs

noncomputable def StartG.logOutputs {M ell : ℕ} (D : StartG M ell) : ℝ :=
  (∑ j, (D.steps j).rate) + D.next.logOutputs

def StartG.a {M ell : ℕ} (D : StartG M ell) : ℕ := D.next.a
def StartG.b {M ell : ℕ} (D : StartG M ell) : ℕ := D.next.b
def StartG.c {M ell : ℕ} (D : StartG M ell) : ℕ := D.next.c

end MME.GlobalCW


