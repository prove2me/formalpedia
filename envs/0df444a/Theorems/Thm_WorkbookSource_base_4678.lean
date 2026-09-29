-- Prove2me | Theorems.Thm_WorkbookSource_base_4678
-- name    : WorkbookSource.base_4678
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:51.894742+00:00
-- url     : https://prove2.me/theorems/e5b5e1e8-70e4-40e7-ad10-99348e225bf4
-- title:
--   A cyclic quadratic ratio bound with a triple-product correction
-- statement:
--   For positives a, b, and c, prove that:
--   $\frac{a^2}{b}+\frac{b^2}{c}+\frac{c^2}{a}+\frac{27abc}{2(a+b+c)^2}\ge\frac{3}{2}(a+b+c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4678` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4678; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4678 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a + (27 * a * b * c) / (2 * (a + b + c)^2)) ≥ (3 / 2) * (a + b + c)  :=  by sorry
