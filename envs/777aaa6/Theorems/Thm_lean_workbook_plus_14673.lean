-- Prove2me | Theorems.Thm_lean_workbook_plus_14673
-- name    : lean_workbook_plus_14673
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7d85fe3c-47fe-4c43-be29-0958ca7a83c5
-- statement:
--   $2<x+\frac{2}{x}<3$ is true for $1<x<2$ ( can be improved as $\frac{3}{2}+\frac{4}{3}<x+\frac{2}{x}<\frac{8}{5}+\frac{5}{4}$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14673 (x : ℝ) (hx: 1<x ∧ x<2) : 2 < x + 2 / x ∧ x + 2 / x < 3   :=  by sorry
