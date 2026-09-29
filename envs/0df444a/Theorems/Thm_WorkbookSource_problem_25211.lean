-- Prove2me | Theorems.Thm_WorkbookSource_problem_25211
-- name    : WorkbookSource.problem_25211
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:52:12.127521+00:00
-- url     : https://prove2.me/theorems/31a8ba59-ff62-4469-aeb4-932451b0839e
-- title:
--   Positivity of pairwise products and reciprocals
-- statement:
--   Prove $ab+bc+ac>0$ and $\frac{1}{ab}+\frac{1}{bc}+\frac{1}{ac}>0$ if $a, b, c$ have the same sign.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25211` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25211; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_25211 (a b c : ℝ) (hab : a * b > 0) (hbc : b * c > 0) (hca : c * a > 0) : a * b + b * c + c * a > 0 ∧ 1 / (a * b) + 1 / (b * c) + 1 / (c * a) > 0  :=  by sorry
