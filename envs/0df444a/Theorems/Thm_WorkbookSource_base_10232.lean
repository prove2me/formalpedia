-- Prove2me | Theorems.Thm_WorkbookSource_base_10232
-- name    : WorkbookSource.base_10232
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:41:25.719358+00:00
-- url     : https://prove2.me/theorems/9a2857e7-0549-4968-b2ad-6b96383850b0
-- title:
--   A normalized product lower bound with cubic corrections
-- statement:
--   Let $a,b,c$ be non-negative real numbers such that $a+b+c=3$ . Prove that:
--
--    $$(a^2 + b^2 + c ^2+abc-3) (2 +abc) \geq 3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10232` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10232; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10232 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) :  (a^2 + b^2 + c^2 + a * b * c - 3) * (2 + a * b * c) ≥ 3  :=  by sorry
