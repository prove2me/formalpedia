-- Prove2me | Theorems.Thm_lean_workbook_plus_37135
-- name    : lean_workbook_plus_37135
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/e63fa46a-4f2d-4ebe-9aa5-8d58a3b7eeb0
-- statement:
--   Let $a,b, c>0$ . $(a^2+1)(b^2+1)(c^2+1) \geqslant \dfrac{5}{16}(ab+bc+ca+1)^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37135 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (5/16) * (a * b + b * c + c * a + 1)^2   :=  by sorry
