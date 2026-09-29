-- Prove2me | Theorems.Thm_lean_workbook_plus_45863
-- name    : lean_workbook_plus_45863
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/31d9d135-ee77-4649-883d-563946a0126e
-- statement:
--   prove that \n $$\frac{a}{1-a^n}+\frac{b}{1-b^n}+\frac{c}{1-c^n}\ge \frac{(n+1)^{1+\frac{1}{n}}}{n}$$\n given $a,b,c$ are positive reals, $n$ is an integer greater than 1, and $a^2+b^2+c^2=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45863 (n : ℤ) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h2 : a^2 + b^2 + c^2 = 1) (hn : n ≥ 2) : (a / (1 - a^n) + b / (1 - b^n) + c / (1 - c^n)) ≥ ((n + 1)^(1 + 1 / n)) / n   :=  by sorry
