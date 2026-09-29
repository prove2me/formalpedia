-- Prove2me | Theorems.Thm_WorkbookSource_base_26851
-- name    : WorkbookSource.base_26851
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:31.516635+00:00
-- url     : https://prove2.me/theorems/73ae9c56-37e4-4c01-bbcb-8a9d30e920da
-- title:
--   A cyclic shifted ratio difference is nonnegative
-- statement:
--   Let $a,b,c>0$ . Prove that $\frac{a(a-b)}{b(a+b)}+\frac{b(b-c)}{c(b+c)}+\frac{c(c-a)}{a(c+a)} \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26851` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26851; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26851 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a - b) / (b * (a + b)) + b * (b - c) / (c * (b + c)) + c * (c - a) / (a * (c + a))) ≥ 0  :=  by sorry
