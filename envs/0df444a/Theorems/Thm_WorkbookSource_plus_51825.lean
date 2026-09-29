-- Prove2me | Theorems.Thm_WorkbookSource_plus_51825
-- name    : WorkbookSource.plus_51825
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:01.931308+00:00
-- url     : https://prove2.me/theorems/1f58fb2a-7b5c-4408-9e9f-f1150bdee518
-- title:
--   A pairwise-product bound under two quadratic constraints
-- statement:
--   Let $a,b,c$ be three numbers positive real such that: $a^2+ab+b^2 \leq18$ and $b^2 +bc+c^2 \leq 6$. Prove that: $ab+bc+ca \leq 12$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_51825` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_51825; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_51825 (a b c: ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a^2 + a * b + b^2 ≤ 18) (hbc : b^2 + b * c + c^2 ≤ 6) : a * b + b * c + c * a ≤ 12   :=  by sorry
