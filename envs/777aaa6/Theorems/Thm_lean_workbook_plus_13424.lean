-- Prove2me | Theorems.Thm_lean_workbook_plus_13424
-- name    : lean_workbook_plus_13424
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/46746f27-1f86-4d48-afcb-a606455f223d
-- statement:
--   If a,b,c are non-negative real numbers, then $ a^2 + b^2 + c^2 - ab - bc - ca \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13424 (a b c: ℝ) : a^2 + b^2 + c^2 - (a * b + b * c + c * a) ≥ 0   :=  by sorry
