-- Prove2me | Theorems.Thm_mme_global_CW_graded_start_sound
-- name    : mme_global_CW_graded_start_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T15:44:11.569637+00:00
-- url     : https://prove2.me/theorems/165ce6d2-eb5b-48f1-8619-e66c854e02e1
-- title:
--   Soundness of the graded global start
-- statement:
--   A graded global start is a genuine unpaired global extraction, split into oriented parts, followed by a graded logarithmic joint recipe on its whole interface. For every graded global start `D` there is an output count at least `exp(D.logOutputs)` such that that many copies of `<D.a, D.b, D.c>` are a restriction of `D.inputs` copies of `CW_5^{\otimes M}`.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: interface tensors fix the level structure exactly and let only complete-split distributions vary (Definitions 3.6 and 4.1); Theorem 6.4, Section 6.6 and Algorithm 1 chain the stages. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_global_CW_graded_start_data
open BigOperators MME MME.TensorObj MME.GlobalCW
set_option autoImplicit false
universe u

theorem mme_global_CW_graded_start_sound {K : Type u} [Field K] {M ell : ℕ} (D : GlobalCW.StartG M ell) :
    ∃ outputs : ℕ, Real.exp D.logOutputs ≤ (outputs : ℝ) ∧
      TensorObj.Restrict (bigAdd (fun _ : Fin outputs ↦ MMObj K D.a D.b D.c))
        (bigAdd (fun _ : Fin D.inputs ↦ (CWObj K 5).kronPow M)) := by sorry
