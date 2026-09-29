-- Prove2me | Theorems.Thm_lean_workbook_plus_46804
-- name    : lean_workbook_plus_46804
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/527a7c21-71f6-41be-b1d7-3110b44a4ac2
-- statement:
--   Show that for positive real numbers $a, b, c$,\n$8a^3+3b^3+3c^3+b^2c+bc^2\geqslant 4(a^2b+ab^2+a^2c+ac^2).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46804 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * a ^ 3 + 3 * b ^ 3 + 3 * c ^ 3 + b ^ 2 * c + b * c ^ 2 ≥ 4 * (a ^ 2 * b + a * b ^ 2 + a ^ 2 * c + a * c ^ 2)   :=  by sorry
