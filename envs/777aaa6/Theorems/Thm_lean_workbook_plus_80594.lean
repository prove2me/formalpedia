-- Prove2me | Theorems.Thm_lean_workbook_plus_80594
-- name    : lean_workbook_plus_80594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/bb7f4070-c56c-4a52-a12c-95100758c83b
-- statement:
--   We have $ \frac{x+y}{2}\geq\frac{2xy}{x+y}\Rightarrow\frac{1}{x+y}\leq\frac{1}{4}\left(\frac{1}{x}+\frac{1}{y}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80594 (x y : ℝ) (hx : x > 0) (hy : y > 0) : (x + y) / 2 ≥ 2 * x * y / (x + y) ↔ 1 / (x + y) ≤ 1 / 4 * (1 / x + 1 / y)   :=  by sorry
