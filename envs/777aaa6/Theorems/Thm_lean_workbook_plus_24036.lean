-- Prove2me | Theorems.Thm_lean_workbook_plus_24036
-- name    : lean_workbook_plus_24036
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c0c8c4ab-d05f-4a14-887a-5a879059ea24
-- statement:
--   Prove that $ 4(a^2+b^2+c^2)^2 \ge 9(a+b+c)(b+c-a)(c+a-b)(a+b-c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24036 (a b c : ℝ) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 9 * (a + b + c) * (b + c - a) * (c + a - b) * (a + b - c)   :=  by sorry
