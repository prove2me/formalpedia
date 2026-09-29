-- Prove2me | Theorems.Thm_lean_workbook_plus_21702
-- name    : lean_workbook_plus_21702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9e837f29-a73a-4143-8fb2-8e2638c0ab72
-- statement:
--   If $a^3+b^3+c^3=(a+b+c)^3$ , prove that $a^5+b^5+c^5=(a+b+c)^5$ where $a,b,c \in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21702 (a b c : ℝ) (ha : a^3 + b^3 + c^3 = (a + b + c)^3) : a^5 + b^5 + c^5 = (a + b + c)^5   :=  by sorry
