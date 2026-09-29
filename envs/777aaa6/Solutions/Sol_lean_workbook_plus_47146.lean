-- Prove2me | solution 1 for lean_workbook_plus_47146
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:30.623+00:00
-- url     : https://prove2.me/submissions/c7e713fc-ec73-4d6f-b1e1-62935a8cfd1f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ a c : ℝ, (1 / (a * c)^(1 / 4) - (a * c)^(1 / 4))^2 + (Real.sqrt a - Real.sqrt c)^2 ≥ 0 := by
  (intros; positivity)
