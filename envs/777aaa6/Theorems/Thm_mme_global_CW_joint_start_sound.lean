-- Prove2me | Theorems.Thm_mme_global_CW_joint_start_sound
-- name    : mme_global_CW_joint_start_sound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:27:56.642991+00:00
-- url     : https://prove2.me/theorems/457d39d1-001d-404f-8d09-f1850389e4f8
-- title:
--   Actual extraction from a global start and joint continuation
-- statement:
--   Explicit finite global hash, repair and exact-type data followed by a joint regional recipe construct actual matrix multiplication copies from a raw CW power, with the stated exponential lower bound on the output count.
-- source:
--   Finite global extraction for More Asymmetry Proposition 5.1 and Theorem 5.3.

import Definitions.Def_mme_global_CW_joint_start_data
open MME MME.TensorObj MME.ProfiledCW MME.GlobalCW
set_option autoImplicit false
universe u

theorem mme_global_CW_joint_start_sound {K : Type u} [Field K] {M ell : ℕ} (D : GlobalCW.Start M ell) :
    ∃ outputs : ℕ, Real.exp D.logOutputs ≤ (outputs : ℝ) ∧
      Restrict (bigAdd (fun _ : Fin outputs ↦ MMObj K D.a D.b D.c))
        (bigAdd (fun _ : Fin D.inputs ↦ (CWObj K 5).kronPow M)) := by
  sorry
