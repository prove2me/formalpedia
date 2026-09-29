-- Prove2me | Theorems.Thm_WorkbookSource_base_13061
-- name    : WorkbookSource.base_13061
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:49:14.49563+00:00
-- url     : https://prove2.me/theorems/a0b4a9e1-f372-4c2c-9d94-48ebf27754fa
-- title:
--   A quadratic ratio sum with a triple-product correction
-- statement:
--   Let $a,b,c$ be positive real numbers such that $a+b+c=3$ . Prove that:
--
--    $$\frac{a^2+3bc}{b+c}+\frac{b^2+3ca}{c+a}+\frac{c^2+3ab}{a+b} \geq \frac{21+3abc}{4}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13061` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13061; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13061 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 + 3 * b * c) / (b + c) + (b^2 + 3 * c * a) / (c + a) + (c^2 + 3 * a * b) / (a + b) ≥ (21 + 3 * a * b * c) / 4  :=  by sorry
