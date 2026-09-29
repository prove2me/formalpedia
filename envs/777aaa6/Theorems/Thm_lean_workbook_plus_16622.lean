-- Prove2me | Theorems.Thm_lean_workbook_plus_16622
-- name    : lean_workbook_plus_16622
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b7ecbae2-f70d-407d-b1c0-cc906a3335e6
-- statement:
--   Let $a,b,$ and $c$ be real numbers. Prove that $(a+b+c)^2\ge 3(ab+bc+ac)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16622 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c)   :=  by sorry
