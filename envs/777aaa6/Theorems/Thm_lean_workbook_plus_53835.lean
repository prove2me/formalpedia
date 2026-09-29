-- Prove2me | Theorems.Thm_lean_workbook_plus_53835
-- name    : lean_workbook_plus_53835
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7afa7814-b3dd-41f0-a8b9-d84d6c5597de
-- statement:
--   $ a^2 +b^2 +c^2 +d^2 +e^2-a(b+c+d+e) =\left(\frac{a}{2}-b \right)^2 +\left(\frac{a}{2} -c \right)^2 +\left(\frac{a}{2} -d\right)^2 +\left(\frac{a}{2} -e\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53835 (a b c d e : ℝ) : a^2 + b^2 + c^2 + d^2 + e^2 - a * (b + c + d + e) = (a / 2 - b) ^ 2 + (a / 2 - c) ^ 2 + (a / 2 - d) ^ 2 + (a / 2 - e) ^ 2   :=  by sorry
