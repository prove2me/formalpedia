-- Prove2me | solution 1 for lean_workbook_plus_50690
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:30:26.698548+00:00
-- url     : https://prove2.me/submissions/b72b43e7-66b1-4c9d-be4a-984c73dca541

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) : x^2 * w * v * (v + w) + y^2 * u * w * (w + u) + z^2 * v * u * (v + u) ≥ 2 * (x * y + z * x + y * z) * u * v * w := by
  have h1 := mul_nonneg hw.le (sq_nonneg (v*x-u*y))
  have h2 := mul_nonneg hv.le (sq_nonneg (w*x-u*z))
  have h3 := mul_nonneg hu.le (sq_nonneg (w*y-v*z))
  nlinarith only [h1,h2,h3]
