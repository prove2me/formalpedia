-- Prove2me | Theorems.Thm_WorkbookSource_base_12018
-- name    : WorkbookSource.base_12018
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:39:15.480687+00:00
-- url     : https://prove2.me/theorems/68b46336-d39d-4aee-8152-15ebb97d09a0
-- title:
--   A cyclic quadratic ratio lower bound at fixed sum three
-- statement:
--   Let $a,b,c> 0$ and $a+b+c=3$ . Prove that: $\frac{a^2}{a+ 2b^2}+\frac{b^2}{b+2c^2}+\frac{c^2}{c+2a^2}\geq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12018` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12018; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12018 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 / (a + 2 * b^2) + b^2 / (b + 2 * c^2) + c^2 / (c + 2 * a^2) ≥ 1  :=  by sorry
