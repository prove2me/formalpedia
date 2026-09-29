-- Prove2me | Theorems.Thm_lean_workbook_plus_49439
-- name    : lean_workbook_plus_49439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/02a5cbe8-5780-49ea-987c-45774a98cc69
-- statement:
--   If $a+b+c=5$ , and $ab+bc+ca=10$ , then prove that $a^{3}+b^{3}+c^{3}-3abc=-25$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49439 (a b c : ℝ) (h1 : a + b + c = 5) (h2 : a * b + b * c + c * a = 10) : a^3 + b^3 + c^3 - 3 * a * b * c = -25   :=  by sorry
