-- Prove2me | Theorems.Thm_lean_workbook_plus_33582
-- name    : lean_workbook_plus_33582
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/398dd3ef-d80f-436b-b033-a25ef55cc0eb
-- statement:
--   Explain why $x^2+bx+c=0$ has real roots only when $b^2-4c\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33582 (b c : ℝ) : (∃ x, x^2 + b * x + c = 0) ↔ b^2 - 4*c >= 0   :=  by sorry
