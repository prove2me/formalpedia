-- Prove2me | Theorems.Thm_lean_workbook_plus_52670
-- name    : lean_workbook_plus_52670
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6a1dffe2-cda0-455d-95c1-9578d03fb1ff
-- statement:
--   Prove the inequality: $a^2(a-(b+c))^2+a^2(b^2+c^2)+(b^2+c^2)(b-c)^2\ge 2a(b+c)(b-c)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52670 (a b c : ℝ) : a^2 * (a - (b + c))^2 + a^2 * (b^2 + c^2) + (b^2 + c^2) * (b - c)^2 ≥ 2 * a * (b + c) * (b - c)^2   :=  by sorry
