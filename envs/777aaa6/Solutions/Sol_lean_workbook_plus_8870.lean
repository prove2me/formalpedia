-- Prove2me | solution 1 for lean_workbook_plus_8870
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:26.549726+00:00
-- url     : https://prove2.me/submissions/6fad9fe7-0e02-4b75-b4c6-b901053071eb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + a * b + b^2) * (a^5 * b + 5 * a^4 * b^2 + 4 * a^3 * b^3 + 3 * a^4 * b * c + 16 * a^3 * b^2 * c + 13 / 3 * a^2 * b^2 * c^2) + (b^2 + b * c + c^2) * (b^5 * c + 5 * b^4 * c^2 + 4 * b^3 * c^3 + 3 * b^4 * c * a + 16 * b^3 * c^2 * a + 13 / 3 * b^2 * c^2 * a^2) + (c^2 + c * a + a^2) * (c^5 * a + 5 * c^4 * a^2 + 4 * c^3 * a^3 + 3 * c^4 * a * b + 16 * c^3 * a^2 * b + 13 / 3 * c^2 * a^2 * b^2) ≥ 0 := by
  (intros; positivity)
