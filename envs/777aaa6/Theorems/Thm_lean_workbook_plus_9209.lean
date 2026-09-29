-- Prove2me | Theorems.Thm_lean_workbook_plus_9209
-- name    : lean_workbook_plus_9209
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c8d7069c-c66d-4bac-ab21-b7ddeaaf0f11
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=abc+2$ . Prove that \n\n $$(a + b)(b + c)(c + a) + 2\geq 2(ab + bc + ca) + 4abc$$\n\n $uvw$ kills it immediately.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9209 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = a * b * c + 2) : (a + b) * (b + c) * (c + a) + 2 ≥ 2 * (a * b + b * c + a * c) + 4 * a * b * c   :=  by sorry
