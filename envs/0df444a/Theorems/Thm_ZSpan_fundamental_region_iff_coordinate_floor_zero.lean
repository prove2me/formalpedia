-- Prove2me | Theorems.Thm_ZSpan_fundamental_region_iff_coordinate_floor_zero
-- name    : ZSpan.fundamental_region_iff_coordinate_floor_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.329542+00:00
-- url     : https://prove2.me/theorems/68dabe64-e89d-421f-9c7e-0ed7822fbea3
-- title:
--   ZSpan.fundamental_region_iff_coordinate_floor_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open ZSpan
variable {E ι K : Type*} [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [NormedAddCommGroup E] [NormedSpace K E] (b : Module.Basis ι K E) [FloorRing K] [Fintype ι]

theorem ZSpan.fundamental_region_iff_coordinate_floor_zero (v : E) : v ∈ fundamentalDomain b ↔ floor b v = 0 := by sorry
