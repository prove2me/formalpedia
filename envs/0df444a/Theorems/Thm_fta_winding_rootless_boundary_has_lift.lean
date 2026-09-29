-- Prove2me | Theorems.Thm_fta_winding_rootless_boundary_has_lift
-- name    : fta_winding_rootless_boundary_has_lift
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-05-22T14:59:44.312626+00:00
-- url     : https://prove2.me/theorems/27fcce43-c4cd-42a9-9446-3f2592cca7d4
-- statement:
--   A rootless polynomial on the closed disk gives a continuous lift of its normalized boundary loop.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Polynomial/Basic.html#Complex.exists_root

import Definitions.Def_fta_winding_infra

theorem fta_winding_rootless_boundary_has_lift (f : Polynomial ℂ) (R : ℝ)
    (hR : 0 < R) (hrootless : FtaClosedDiskRootless f R) :
    FtaHasLift (FtaBoundaryLoop f R) := by
  sorry
