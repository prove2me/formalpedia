-- Prove2me | Theorems.Thm_lean_workbook_plus_4742
-- name    : lean_workbook_plus_4742
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9b1c8295-b4ce-4231-9bf5-5999d981bf54
-- statement:
--   Prove $ab + bc + ca \le \dfrac{(a + b + c)^2}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4742 (a b c : ℝ) : a * b + b * c + c * a ≤ (a + b + c) ^ 2 / 3   :=  by sorry
