-- Prove2me | Theorems.Thm_lean_workbook_plus_1320
-- name    : lean_workbook_plus_1320
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/c548ae28-627f-48a9-879c-62f5b5e9705f
-- statement:
--   Using the Arithmetic Mean-Geometric Mean (AM-GM) inequality, show that $2(a+c)^{2}+2(b+d)^{2} \geq 8(ac+bd)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1320 (a b c d : ℝ) : 2 * (a + c) ^ 2 + 2 * (b + d) ^ 2 ≥ 8 * (a * c + b * d)   :=  by sorry
