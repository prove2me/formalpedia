-- Prove2me | Theorems.Thm_lean_workbook_plus_13790
-- name    : lean_workbook_plus_13790
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/2cb2e204-832d-4de0-bc1c-47671b167a9e
-- statement:
--   Prove that for real numbers $a, b, c, d$, the inequality $a^3(b + c + d) + b^3(a + c + d) + c^3(a + b + d) + d^3(a + b + c) \leq \frac{3}{4}(a^2 + b^2 + c^2 + d^2)^2$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13790 (a b c d : ℝ) : a ^ 3 * (b + c + d) + b ^ 3 * (a + c + d) + c ^ 3 * (a + b + d) + d ^ 3 * (a + b + c) ≤ (3 / 4 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2   :=  by sorry
