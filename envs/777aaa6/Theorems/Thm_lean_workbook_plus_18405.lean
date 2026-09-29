-- Prove2me | Theorems.Thm_lean_workbook_plus_18405
-- name    : lean_workbook_plus_18405
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f6707acb-e211-4d62-9c07-c86ad95eda17
-- statement:
--   Given that A, B, C are angles of a triangle, prove that $-cosC*sinC +sinC*cosC = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18405 (A B C : ℝ) (hx: A + B + C = π) (hb : 0 < A ∧ 0 < B ∧ 0 < C) (hab : A + B > C) (hbc : B + C > A) (hca : A + C > B) : -cos C * sin C + sin C * cos C = 0   :=  by sorry
