-- Prove2me | Theorems.Thm_lean_workbook_plus_80941
-- name    : lean_workbook_plus_80941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/3b1189fe-8251-4dcc-984c-574e87399d31
-- statement:
--   Prove that for real numbers $x, y$ with $|x| \leq 1$ and $|y| \leq 1$, the following equality holds:\n$x^2 + y^2 - 2x^2y^2 + 2xy\sqrt{1-x^2}\sqrt{1-y^2} = (x\sqrt{1-y^2} + y\sqrt{1-x^2})^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80941 (x y : ℝ) (hx : abs x ≤ 1) (hy : abs y ≤ 1) : x^2 + y^2 - 2 * x^2 * y^2 + 2 * x * y * Real.sqrt (1 - x^2) * Real.sqrt (1 - y^2) = (x * Real.sqrt (1 - y^2) + y * Real.sqrt (1 - x^2))^2   :=  by sorry
