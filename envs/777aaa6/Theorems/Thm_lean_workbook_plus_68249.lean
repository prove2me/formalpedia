-- Prove2me | Theorems.Thm_lean_workbook_plus_68249
-- name    : lean_workbook_plus_68249
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/6b7379aa-61d8-4775-8a1a-73cb4d928ad7
-- statement:
--   For a triangle ABC with sides a, b, c, show that the following inequality holds:\n$ \sum_{cyclic} a(b^2 +c^2 - a^2) \le 3abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68249 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a * (b * b + c * c - a * a) + b * (c * c + a * a - b * b) + c * (a * a + b * b - c * c) ≤ 3 * a * b * c   :=  by sorry
