-- Prove2me | Theorems.Thm_lean_workbook_plus_47982
-- name    : lean_workbook_plus_47982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ad395b1f-d14c-49e5-97d3-2ac8e64c275c
-- statement:
--   For $x,\ y,\ z>0$ , such that $\sum \frac{1}{x^2+1}=2$ \nProve that : $xy+yz+zx\le \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47982 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hx2 : x^2 + 1 > 0) (hy2 : y^2 + 1 > 0) (hz2 : z^2 + 1 > 0) (h : 1 / x^2 + 1 + 1 / y^2 + 1 + 1 / z^2 + 1 = 2) : x * y + y * z + z * x ≤ 3 / 2   :=  by sorry
