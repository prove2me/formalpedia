-- Prove2me | Theorems.Thm_lean_workbook_plus_53618
-- name    : lean_workbook_plus_53618
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/c17e5640-e548-49be-9136-31505879fc7e
-- statement:
--   For all real, positive, and distinct a, b, and c, prove that $a^2(b+c) + b^2(c+a) + c^2(a+b) < 2(a^3 + b^3 + c^3)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53618 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hbc : b ≠ c) (hca : a ≠ c) : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) < 2 * (a^3 + b^3 + c^3)   :=  by sorry
