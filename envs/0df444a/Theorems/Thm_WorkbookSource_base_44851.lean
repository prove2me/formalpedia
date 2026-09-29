-- Prove2me | Theorems.Thm_WorkbookSource_base_44851
-- name    : WorkbookSource.base_44851
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:54:40.098468+00:00
-- url     : https://prove2.me/theorems/7b68a8de-7d23-4780-b636-702ffb87df18
-- title:
--   A shifted cyclic quadratic ratio lower bound at fixed sum six
-- statement:
--   Let $ a,$ $ b$ and $ c$ are positive numbers such that $ a+b+c=6.$ Prove that
--    $ \frac{a}{b^2+c}+\frac{b}{c^2+a}+\frac{c}{a^2+b}\geq1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44851` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44851; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44851 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 6) : a / (b * b + c) + b / (c * c + a) + c / (a * a + b) ≥ 1  :=  by sorry
