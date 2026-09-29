-- Prove2me | solution 1 for lean_workbook_plus_4865
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:19.094991+00:00
-- url     : https://prove2.me/submissions/c54a8d25-e841-44af-8725-724ebd74b628

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (w : ℝ)
  (h₀ : w ≠ 0) :
  ((5 * w / 8 + 5 * w / 12 + 5 * w / 16) / w) = 65 / 48 := by
  (intros; field_simp; ring)
