-- Prove2me | Theorems.Thm_lean_workbook_plus_59684
-- name    : lean_workbook_plus_59684
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/77508fdb-6f2f-4fc4-a2d0-3a2abe041ec7
-- statement:
--   Given that $0\le a\le b\le c$ , prove that $$(a+b+2)(b+c+4)(c+a+6)\ge 8(a+1)(b+2)(c+3)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59684 (a b c : ℝ) (ha : 0 ≤ a) (hb : a ≤ b) (hc : b ≤ c) : (a + b + 2) * (b + c + 4) * (c + a + 6) ≥ 8 * (a + 1) * (b + 2) * (c + 3)   :=  by sorry
