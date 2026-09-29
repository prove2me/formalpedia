-- Prove2me | solution 1 for lean_workbook_plus_18969
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:47.068201+00:00
-- url     : https://prove2.me/submissions/48b9e8e6-3031-4a12-89aa-c3629dd1f266

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ y z : ℝ, y^6 + z^6 ≥ y * z * (y^4 + z^4) := by
  intro y z
  nlinarith only [sq_nonneg ((y-z)*(y^2+y*z)),sq_nonneg ((y-z)*(z^2+y*z)),sq_nonneg ((y-z)*y^2),sq_nonneg ((y-z)*z^2)]
