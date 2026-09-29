-- Prove2me | Theorems.Thm_lean_workbook_plus_2743
-- name    : lean_workbook_plus_2743
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cc026c59-3de2-400d-aa6b-5bd208d91d61
-- statement:
--   It's equivalent to \n $ 3\sum{a^4(b^2 + c^2) + 6a^2b^2c^2\geq 4abc\sum_{cyc}{a^2(b + c)}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2743 (a b c : ℝ) : 3 * (a ^ 4 * (b ^ 2 + c ^ 2) + b ^ 4 * (c ^ 2 + a ^ 2) + c ^ 4 * (a ^ 2 + b ^ 2)) + 6 * a ^ 2 * b ^ 2 * c ^ 2 ≥ 4 * a * b * c * (a ^ 2 * (b + c) + b ^ 2 * (c + a) + c ^ 2 * (a + b))   :=  by sorry
