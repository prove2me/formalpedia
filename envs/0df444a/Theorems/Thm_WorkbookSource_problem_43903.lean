-- Prove2me | Theorems.Thm_WorkbookSource_problem_43903
-- name    : WorkbookSource.problem_43903
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:02:19.797396+00:00
-- url     : https://prove2.me/theorems/55534da6-fbd5-4b3c-9539-c7443fecddb3
-- title:
--   Addition commutes with averaging
-- statement:
--   Prove or disprove the distributive property of addition over averaging: $a+\frac{b+c}{2}=\frac{a+b}{2}+\frac{a+c}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43903` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43903; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_43903 (a b c : ℝ) : a + (b + c) / 2 = (a + b) / 2 + (a + c) / 2  :=  by sorry
