-- Prove2me | Theorems.Thm_periodic_packing_supremum_eq_unit_separation
-- name    : periodic_packing_supremum_eq_unit_separation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:03.329542+00:00
-- url     : https://prove2.me/theorems/e9d4cd08-49d6-4242-9a01-8354ab86009a
-- title:
--   periodic_packing_supremum_eq_unit_separation
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology
variable {d : ℕ}

theorem periodic_packing_supremum_eq_unit_separation :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.upperPackingDensity := by sorry
