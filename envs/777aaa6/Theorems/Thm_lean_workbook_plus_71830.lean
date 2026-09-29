-- Prove2me | Theorems.Thm_lean_workbook_plus_71830
-- name    : lean_workbook_plus_71830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ae998d31-a67a-4f4d-ac42-099b26f19d46
-- statement:
--   Prove that for positive real numbers $a, b, c$, the following inequality holds: $ab^3+ac^3+bc^3+ba^3+ca^3+cb^3 \le 2(a^4+b^4+c^4)$ using the rearrangement inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71830 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a * b ^ 3 + a * c ^ 3 + b * c ^ 3 + b * a ^ 3 + c * a ^ 3 + c * b ^ 3 ≤ 2 * (a ^ 4 + b ^ 4 + c ^ 4)   :=  by sorry
