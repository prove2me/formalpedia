-- Prove2me | Theorems.Thm_lean_workbook_plus_43133
-- name    : lean_workbook_plus_43133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/fd8cd9ea-03be-40be-9192-c1275996bc08
-- statement:
--   The following is stronger $\sum_{cycl}(a^{2}-ab+b^{2})(b^{2}-bc+c^{2}) \ge \frac{1}{3}(a^{2}+b^{2}+c^{2})^{2}$ Also, it is true for all reals $a,b$ and $c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43133 (a b c : ℝ) : (a^2 - a * b + b^2) * (b^2 - b * c + c^2) + (b^2 - b * c + c^2) * (c^2 - c * a + a^2) + (c^2 - c * a + a^2) * (a^2 - a * b + b^2) ≥ 1/3 * (a^2 + b^2 + c^2)^2   :=  by sorry
