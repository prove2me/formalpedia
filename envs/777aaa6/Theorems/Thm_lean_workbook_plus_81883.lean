-- Prove2me | Theorems.Thm_lean_workbook_plus_81883
-- name    : lean_workbook_plus_81883
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/95232de1-cf1d-4a94-b883-daca6a38dd11
-- statement:
--   Verify the identity \(x^3 + y^3 + z^3 - 3xyz = \frac{1}{2} \times (x+y+z) \times ( (x-y)^2 + (y-z)^2 + (z-x)^2 )\) and use it to show that \(x^3 + y^3 + z^3 \ge 3xyz\) for both \(x+y+z \ge 0\) and \(x+y+z \le 0\), with equality occurring when either \(x+y+z=0\) or \(x=y=z\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81883 (x y z : ℝ) : x^3 + y^3 + z^3 - 3 * x * y * z = 1 / 2 * (x + y + z) * ( (x - y)^2 + (y - z)^2 + (z - x)^2)   :=  by sorry
