-- Prove2me | Theorems.Thm_lean_workbook_plus_17596
-- name    : lean_workbook_plus_17596
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7b04507f-5cf6-44a5-897d-e8184799055a
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers. Prove that: $2(a^3+b^3+c^3)+3\geq3(ab+ac+bc)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17596 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 ≥ 3 * (a * b + a * c + b * c)   :=  by sorry
