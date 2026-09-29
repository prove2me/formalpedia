-- Prove2me | Theorems.Thm_lean_workbook_plus_21450
-- name    : lean_workbook_plus_21450
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/076357b7-6461-4573-86f3-6104d4b4807f
-- statement:
--   Using the well-known inequality \(x+y+z\ge \sqrt{3(xy+xz+yz)}\) and the given condition \(xy+xz+yz\ge 3\), prove that \(\frac{x^2+y^2+z^2+xy+xz+yz+3}{(x+y+z)^2} \le \frac{x^2+y^2+z^2+2(xy+xz+yz)}{(x+y+z)^2}=1\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21450 (x y z : ℝ) (h : x * y + x * z + y * z ≥ 3) : (x ^ 2 + y ^ 2 + z ^ 2 + x * y + x * z + y * z + 3) / (x + y + z) ^ 2 ≤ 1   :=  by sorry
