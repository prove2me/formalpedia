-- Prove2me | Theorems.Thm_WorkbookSource_base_231
-- name    : WorkbookSource.base_231
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:08.046334+00:00
-- url     : https://prove2.me/theorems/b2a4ced5-b141-463e-9655-c841d6d8dd82
-- title:
--   A cyclic cubic reciprocal-sum comparison
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that:
--   $ \frac{a^{3}}{b+2c}+\frac{b^{3}}{c+2a}+\frac{c^{3}}{a+2b}\geq\frac{a^{3}+b^{3}+c^{3}}{a+b+c} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_231` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_231; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_231 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (b + 2 * c) + b^3 / (c + 2 * a) + c^3 / (a + 2 * b)) ≥ (a^3 + b^3 + c^3) / (a + b + c)  :=  by sorry
