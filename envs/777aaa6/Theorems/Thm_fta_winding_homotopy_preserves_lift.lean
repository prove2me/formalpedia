-- Prove2me | Theorems.Thm_fta_winding_homotopy_preserves_lift
-- name    : fta_winding_homotopy_preserves_lift
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-05-22T14:59:52.027643+00:00
-- url     : https://prove2.me/theorems/097c52c7-608c-4ae4-a065-8652c0ce665a
-- statement:
--   Continuous liftability is preserved under circle homotopy.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Definitions.Def_fta_winding_infra

theorem fta_winding_homotopy_preserves_lift (γ δ : FtaCircle → Circle)
    (hhom : FtaCircleHomotopic γ δ) (hlift : FtaHasLift γ) :
    FtaHasLift δ := by
  sorry
