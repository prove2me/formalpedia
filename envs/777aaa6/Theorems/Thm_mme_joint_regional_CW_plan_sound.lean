-- Prove2me | Theorems.Thm_mme_joint_regional_CW_plan_sound
-- name    : mme_joint_regional_CW_plan_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T00:52:25.244967+00:00
-- url     : https://prove2.me/theorems/5c5b4265-ae49-4003-80f5-a994aa1b2986
-- title:
--   Soundness of joint regional CW plans
-- statement:
--   A joint regional plan extends a regional plan by a joint regional stage:
--
--   - the $N$ positions are split into parts;
--   - each part takes its own hashing step in its own orientation;
--   - a single continuation plan then runs on all $N$ positions, with a predicate that implies every part's step target.
--
--   This is the shape of More Asymmetry, Theorem 6.4 and Algorithm 1. Every constituent stage divides each term into six regions, hashes each region jointly over all terms, takes the tensor product of the six outputs, and hands the whole product interface tensor to the next stage.
--
--   For every joint regional plan $D$ with root predicate $P$, $D.\mathrm{outputs}$ copies of $\langle D.a, D.b, D.c\rangle$ are a restriction of $D.\mathrm{inputs}$ copies of the $P$-projection of $CW_5^{\otimes N}$.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: Theorem 5.3 (the global stage outputs one interface tensor over all six regions), Theorem 6.4 and Section 6.6 (each constituent stage divides every term into six regions, hashes each region jointly over all terms, and takes the tensor product of the six outputs), and Algorithm 1 in Section 7. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_joint_regional_CW_plan_data
open MME MME.TensorObj MME.ProfiledCW
set_option autoImplicit false
universe u

theorem mme_joint_regional_CW_plan_sound {K : Type u} [Field K] {N ell : ℕ} {P : Predicate N}
    (D : JointPlan N ell P) :
    TensorObj.Restrict (bigAdd (fun _ : Fin D.outputs ↦ MMObj K D.a D.b D.c))
      (bigAdd (fun _ : Fin D.inputs ↦ tensor K P)) := by sorry
