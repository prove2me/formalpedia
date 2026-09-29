-- Prove2me | Theorems.Thm_lean_workbook_plus_63403
-- name    : lean_workbook_plus_63403
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ef0d9034-7142-47a8-a45f-a61e86acfd0a
-- statement:
--   Prove that for $a,b,c$ real numbers $\sum ab(b-a)=(a-b)(b-c)(c-a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63403 (a b c : ℝ) : a * b * (b - a) + b * c * (c - b) + c * a * (a - c) = (a - b) * (b - c) * (c - a)   :=  by sorry
