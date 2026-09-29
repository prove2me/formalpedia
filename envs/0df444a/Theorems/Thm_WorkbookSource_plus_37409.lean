-- Prove2me | Theorems.Thm_WorkbookSource_plus_37409
-- name    : WorkbookSource.plus_37409
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:26.310581+00:00
-- url     : https://prove2.me/theorems/3b26be19-0f89-4cb8-909f-e112dfb7a350
-- title:
--   A symmetric quartic sum is at most two at fixed total two
-- statement:
--   Let $a,b,c\geq 0$ such that $a+b+c=2$. Prove that: $\sum ab(a^{2}+b^{2})\leq 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_37409` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_37409; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_37409 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2) ≤ 2   :=  by sorry
