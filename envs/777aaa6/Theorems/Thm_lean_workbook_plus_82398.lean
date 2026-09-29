-- Prove2me | Theorems.Thm_lean_workbook_plus_82398
-- name    : lean_workbook_plus_82398
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/55954ac5-2905-415b-b613-be2782dbaac8
-- statement:
--   Given the roots $a, b, c$ of $P(x) = x^3 - 2x^2 + 3x - 4$, derive the equation $S_3 - 2S_2 + 3S_1 - 4S_0 = 0$ by summing $P(a) = 0$, $P(b) = 0$, and $P(c) = 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82398 (a b c : ℂ) (ha : a^3 - 2*a^2 + 3*a - 4 = 0) (hb : b^3 - 2*b^2 + 3*b - 4 = 0) (hc : c^3 - 2*c^2 + 3*c - 4 = 0) : a^3 + b^3 + c^3 - 2 * (a^2 + b^2 + c^2) + 3 * (a + b + c) - 4 * 3 = 0   :=  by sorry
