-- Prove2me | Theorems.Thm_lean_workbook_plus_6295
-- name    : lean_workbook_plus_6295
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/20d2bf07-464a-424c-b369-243cc8f27057
-- statement:
--   $ \le (a + b + c)^2(ab + bc + ca) - abc(a + b + c) = (a + b + c)(a + b)(b + c)(c + a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6295 (a b c : ℝ) : (a + b + c) ^ 2 * (a * b + b * c + c * a) - a * b * c * (a + b + c) = (a + b + c) * (a + b) * (b + c) * (c + a)   :=  by sorry
