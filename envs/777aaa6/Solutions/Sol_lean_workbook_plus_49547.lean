-- Prove2me | solution 1 for lean_workbook_plus_49547
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:36:08.824176+00:00
-- url     : https://prove2.me/submissions/4534cda7-ee48-45f5-be18-12a513749e6b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r s t : ℝ) : (r + s + t) / 3 ≥ (r * s * t)^(1/3) → r + s + t ≥ 3 * (r * s * t)^(1/3) := by
  (intros; linarith)
