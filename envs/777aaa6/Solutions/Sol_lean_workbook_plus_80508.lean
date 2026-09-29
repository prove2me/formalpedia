-- Prove2me | solution 1 for lean_workbook_plus_80508
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:56.643101+00:00
-- url     : https://prove2.me/submissions/d0245f33-3c59-462d-8ce5-2fd47038c1b2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c k : ℝ) : (a^3 * k^4 + a^3 + 3 * a * k^4 * c^2 + 6 * a * k^2 * c^2 + 8 * a * k * c^2 + b^3 * k^4 - b^2 * c - b^2 * a - 2 * k^2 * a^3 + 6 * k^2 * c * a^2 - 8 * k * c * a^2 + 6 * b^2 * c * k^2 - b * a^2 - b * c^2 - 2 * b^3 * k^2 - 21 * b * k^4 * c + 3 * b * k^4 * c^2 + 3 * b * k^4 * a^2 + b * a * c - 30 * b * k^2 * c * a + 3 * b^2 * a * k^4 + 8 * b^2 * k * c + 6 * b^2 * a * k^2 - 8 * b^2 * k * a - 8 * b * k * c^2 + 6 * b * k^2 * c^2 + 3 * b^2 * k^4 * c + 6 * b * k^2 * a^2 + 8 * b * k * a^2 + b^3 + c^3 - a * c^2 - a^2 * c + c^3 * k^4 - 2 * k^2 * c^3 + 3 * k^4 * c * a^2)^2 ≥ 0 := by
  (intros; positivity)
