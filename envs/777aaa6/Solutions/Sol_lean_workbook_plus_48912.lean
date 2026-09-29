-- Prove2me | solution 1 for lean_workbook_plus_48912
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:28.400649+00:00
-- url     : https://prove2.me/submissions/580e47a0-1e8e-4e8f-a4f3-74f74b9dfb98

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r s t : ℝ) :
  r^3 + s^3 + t^3 - 3 * r * s * t =
    (r + s + t) * ((r + s + t)^2 - 3 * (r * s + s * t + r * t)) := by
  (intros; linarith)
