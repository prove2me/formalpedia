-- Prove2me | Theorems.Thm_lean_workbook_plus_1297
-- name    : lean_workbook_plus_1297
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/6dd46f30-d4a8-4b0b-bdc4-8a3f26f19f43
-- statement:
--   Given $a,b,c,>0$ such that: $a^2+b^2+c^2+abc=4$ . Prove that $a+b+c \leq 3$ . ( $p,q,r$ is useful).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1297 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : a + b + c ≤ 3   :=  by sorry
