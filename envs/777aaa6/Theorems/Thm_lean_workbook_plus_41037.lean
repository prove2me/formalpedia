-- Prove2me | Theorems.Thm_lean_workbook_plus_41037
-- name    : lean_workbook_plus_41037
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/dc635d4e-d637-4ef4-b6e7-20df7eaa400a
-- statement:
--   Prove $a^2b+b^2c+c^2a \le \sqrt{\frac{(a^2+b^2+c^2)^3}{3} }$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41037 (a b c : ℝ) : a^2 * b + b^2 * c + c^2 * a ≤ Real.sqrt ((a^2 + b^2 + c^2)^3 / 3)   :=  by sorry
