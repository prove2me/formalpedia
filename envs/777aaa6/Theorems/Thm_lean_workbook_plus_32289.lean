-- Prove2me | Theorems.Thm_lean_workbook_plus_32289
-- name    : lean_workbook_plus_32289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/de9ba370-9c19-4be1-bffe-b91d42c336fd
-- statement:
--   Let $a,b$ be positive reals. Prove that \n ${{a}^{4}}+{{b}^{4}}+\frac{1}{4}\ge 2ab(1-ab)\Leftrightarrow 4{{({{a}^{2}}-{{b}^{2}})}^{2}}+{{(4ab-1)}^{2}}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32289 (a b : ℝ) : a^4 + b^4 + 1 / 4 ≥ 2 * a * b * (1 - a * b) ↔ 4 * (a^2 - b^2)^2 + (4 * a * b - 1)^2 ≥ 0   :=  by sorry
