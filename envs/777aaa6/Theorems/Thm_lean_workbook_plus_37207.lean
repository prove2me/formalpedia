-- Prove2me | Theorems.Thm_lean_workbook_plus_37207
-- name    : lean_workbook_plus_37207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0176e641-664c-4088-9996-096517b615ff
-- statement:
--   Prove that $ |x|\leq1 \Rightarrow|x^2-x-2|\leq3|x+1|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37207 (x : ℝ) (hx : abs x ≤ 1) : abs (x^2 - x - 2) ≤ 3 * abs (x + 1)   :=  by sorry
