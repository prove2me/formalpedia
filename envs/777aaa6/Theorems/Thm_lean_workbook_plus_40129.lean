-- Prove2me | Theorems.Thm_lean_workbook_plus_40129
-- name    : lean_workbook_plus_40129
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a46bc313-ec2e-41e4-9c44-6bdb1b225009
-- statement:
--   Prove that $\frac{z}{z^2 + 1} \le \frac{2}{5}$ for $z \ge 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40129 (z : ℝ) (h : z ≥ 2) : z / (z^2 + 1) ≤ 2/5   :=  by sorry
