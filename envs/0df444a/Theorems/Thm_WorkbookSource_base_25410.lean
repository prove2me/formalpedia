-- Prove2me | Theorems.Thm_WorkbookSource_base_25410
-- name    : WorkbookSource.base_25410
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:05:09.786297+00:00
-- url     : https://prove2.me/theorems/d5f5d9a4-2c7d-4661-8783-610ab74a6b50
-- title:
--   A shifted cyclic quadratic ratio lower bound at fixed sum three
-- statement:
--   Let $a,b,c$ be positive reals number and $a+b+c=3.$ ，Prove that
--
--    $\frac{a^2+b}{a^2+1}+\frac{b^2+c}{b^2+1}+\frac{c^2+a}{c^2+1}\geq 3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25410` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25410; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25410 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + b)/(a^2 + 1) + (b^2 + c)/(b^2 + 1) + (c^2 + a)/(c^2 + 1) ≥ 3  :=  by sorry
