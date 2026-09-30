-- Prove2me | solution 1 for lean_workbook_plus_56265
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:06.957269+00:00
-- url     : https://prove2.me/submissions/7850a954-321d-42b8-b5ad-3e5c52c5cee2

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c x y z : ℝ) (ha : a = 1 + x) (hb : b = 1 + y) (hc : c = 1 + z) (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) : a^2 + b^2 + c^2 + 2 * a * b * c + 3 - (1 + a) * (1 + b) * (1 + c) = x^2 + y^2 + z^2 + x * y * z := by
  subst ha hb hc
  ring
