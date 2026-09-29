-- Prove2me | Theorems.Thm_lean_workbook_plus_17628
-- name    : lean_workbook_plus_17628
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7bed0a51-fa00-44b3-b1ee-3cbad139776a
-- statement:
--   Use AM-GM we have $\frac{a^2}{bc} \geq \frac{4a^2}{(b+c)^2}\Leftrightarrow (b+c)^2 \geq 4bc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17628 (a b c : ℝ) : (b + c) ^ 2 ≥ 4 * b * c   :=  by sorry
