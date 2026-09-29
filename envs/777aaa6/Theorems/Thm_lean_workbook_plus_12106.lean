-- Prove2me | Theorems.Thm_lean_workbook_plus_12106
-- name    : lean_workbook_plus_12106
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/26551301-e44f-499f-b904-3f9c154fce03
-- statement:
--   Prove that $\sin(a)\cos(a)+\sin(b)\cos(b)=\sin(a+b)\cos(a-b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12106 (a b : ℝ) : sin a * cos a + sin b * cos b = sin (a + b) * cos (a - b)   :=  by sorry
