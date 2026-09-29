-- Prove2me | Theorems.Thm_lean_workbook_plus_47000
-- name    : lean_workbook_plus_47000
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/8a49fdf0-987b-4435-9c51-7b6c189b6f60
-- statement:
--   Let $a, b, c$ be positive real numbers. Prove that \n $ a^3b^4 + b^3c^4 + c^3a^4 \hspace{0.25cm} \geq \hspace{0.25cm} 2(abc)(ab+bc+ca)^2 - 5(abc)^2 (a+b+c) $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47000 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 * b^4 + b^3 * c^4 + c^3 * a^4 >= 2 * a * b * c * (a * b + b * c + c * a)^2 - 5 * (a * b * c)^2 * (a + b + c)   :=  by sorry
