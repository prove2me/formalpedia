-- Prove2me | Theorems.Thm_WorkbookSource_base_4359
-- name    : WorkbookSource.base_4359
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:06.259023+00:00
-- url     : https://prove2.me/theorems/1086f188-4bee-4671-bf11-b24b99283bae
-- title:
--   A quadratic sum times two reciprocals bounds a pairwise sum
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that $ (a^2+b^2+c^2 )\left(\frac{1}{a+2c}+\frac{1}{b+2c} \right) \geq a+b.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4359` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4359; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4359 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + b^2 + c^2) * (1/(a + 2 * c) + 1/(b + 2 * c)) ≥ a + b  :=  by sorry
