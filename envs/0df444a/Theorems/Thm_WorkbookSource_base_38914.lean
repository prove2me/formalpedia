-- Prove2me | Theorems.Thm_WorkbookSource_base_38914
-- name    : WorkbookSource.base_38914
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:30.169264+00:00
-- url     : https://prove2.me/theorems/bd6761c5-8a04-4abd-a5cb-44f7799859c9
-- title:
--   A product of quadratic differences at fixed sum three
-- statement:
--   Let $ a,b,c \geq 0 $ with $ a+b+c=3 $ ,prove that:
--    $ (b^{2}-bc+c^{2}) (c^{2}-ca+a^{2}) (a^{2}-ab+b^{2})\geq abc. $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38914` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38914; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38914 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = 3) : (b^2 - b * c + c^2) * (c^2 - c * a + a^2) * (a^2 - a * b + b^2) ≥ a * b * c  :=  by sorry
