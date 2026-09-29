-- Prove2me | Theorems.Thm_lean_workbook_plus_17283
-- name    : lean_workbook_plus_17283
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/999a8443-3df5-41da-97c9-e2be8a26adc5
-- statement:
--   Let $a,b,c$ be three positive real numbers. Show that $a^2+b^2+c^2\ge bc+ca+ab+3(a-b)(b-c).$ When does the equality occur?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17283 (a b c : ℝ) : a^2 + b^2 + c^2 ≥ b * c + c * a + a * b + 3 * (a - b) * (b - c)   :=  by sorry
