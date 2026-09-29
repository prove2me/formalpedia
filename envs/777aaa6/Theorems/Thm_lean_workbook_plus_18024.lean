-- Prove2me | Theorems.Thm_lean_workbook_plus_18024
-- name    : lean_workbook_plus_18024
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/773034e7-2dc0-4a25-a6ab-e164a261f912
-- statement:
--   Prove Schur's Inequality in third degree: $a^3 + b^3 + c^3 + 3abc \geq (a+b+c)^3$ for positive real numbers a, b, and c.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18024 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 + 3 * a * b * c ≥ (a + b + c)^3   :=  by sorry
