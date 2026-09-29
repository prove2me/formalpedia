-- Prove2me | Theorems.Thm_mme_global_CW_exact_stage_extraction
-- name    : mme_global_CW_exact_stage_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:27:28.753071+00:00
-- url     : https://prove2.me/theorems/908aeace-0b01-432c-8dff-e7314b7bf0f3
-- title:
--   Finite usable global CW stage extraction
-- statement:
--   Selects usable, X-isolated original global blocks from explicit finite hash incidence bounds, repairs holes and constructs the certified number of copies as an actual tensor restriction.
-- source:
--   Finite global extraction for More Asymmetry Proposition 5.1 and Theorem 5.3.

import Definitions.Def_mme_global_CW_joint_start_data
open MME MME.TensorObj MME.ProfiledCW MME.GlobalCW
set_option autoImplicit false
universe u

theorem mme_global_CW_exact_stage_extraction {K : Type u} [Field K] {ell M : ℕ}
    (D : ExactStage ell M) (hbudget : D.hash.Budget) :
    Restrict (bigAdd (fun _ : Fin D.copies ↦ tensor K D.output))
      (tensor K (fun _ (_ : FineWord M) ↦ True)) := by
  sorry
