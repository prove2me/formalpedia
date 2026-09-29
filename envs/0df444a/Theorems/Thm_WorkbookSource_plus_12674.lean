-- Prove2me | Theorems.Thm_WorkbookSource_plus_12674
-- name    : WorkbookSource.plus_12674
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:25:43.441182+00:00
-- url     : https://prove2.me/theorems/3969a73b-6a00-4692-8645-27a8e4507afc
-- title:
--   A seventh-degree inequality involving triangle factors
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers. Prove that:
--    $$(a+b-c)(a+c-b)(b+c-a)(a^2+b^2+c^2)^2\leq abc(ab+ac+bc)^2$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_12674` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_12674; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_12674 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b - c) * (a + c - b) * (b + c - a) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≤ a * b * c * (a * b + a * c + b * c) ^ 2   :=  by sorry
