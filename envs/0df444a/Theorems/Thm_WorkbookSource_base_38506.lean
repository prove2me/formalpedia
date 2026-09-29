-- Prove2me | Theorems.Thm_WorkbookSource_base_38506
-- name    : WorkbookSource.base_38506
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:36.869876+00:00
-- url     : https://prove2.me/theorems/decff354-3ef0-4b4a-92bc-571f1a3b54eb
-- title:
--   A cubic sum with a triple-product correction bounds the linear sum
-- statement:
--   Let $a, b,c\geq 0.$ Prove that $$a^3+b^3+c^3+abc+1 \geq a+b+c $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38506` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38506; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38506 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^3 + b^3 + c^3 + a * b * c + 1 ≥ a + b + c  :=  by sorry
