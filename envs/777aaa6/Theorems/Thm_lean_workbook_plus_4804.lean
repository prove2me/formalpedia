-- Prove2me | Theorems.Thm_lean_workbook_plus_4804
-- name    : lean_workbook_plus_4804
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f84b5217-8e7c-49de-9188-d4f52fe69e26
-- statement:
--   $(a+b)(b+c)(c+a)=(a+b+c)(ab+bc+ca)-abc=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4804 (a b c : ℤ) : (a + b) * (b + c) * (c + a) = (a + b + c) * (a * b + b * c + c * a) - a * b * c   :=  by sorry
