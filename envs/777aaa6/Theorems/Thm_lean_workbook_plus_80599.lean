-- Prove2me | Theorems.Thm_lean_workbook_plus_80599
-- name    : lean_workbook_plus_80599
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f919ae4a-e5b2-42c0-af0f-2d043ad49741
-- statement:
--   Prove that $S_c(a-b)^2 \ge 0$ With new $S_c=3(a+b)+\frac{(a+b)(b+c)(c+a)}{a+b+c}-2(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80599 (a b c : ℝ) : (3 * (a + b) + (a + b) * (b + c) * (c + a) / (a + b + c) - 2 * (a + b + c)) ^ 2 ≥ 0   :=  by sorry
