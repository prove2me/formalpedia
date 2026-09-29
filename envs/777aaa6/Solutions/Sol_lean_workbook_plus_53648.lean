-- Prove2me | solution 1 for lean_workbook_plus_53648
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:00.928645+00:00
-- url     : https://prove2.me/submissions/2fafeae8-2ee3-4551-8dd8-750695dd8874

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 ≥ x ^ 3 * y + y ^ 3 * z + z ^ 3 * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
