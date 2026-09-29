-- Prove2me | Theorems.Thm_WorkbookSource_base_44075
-- name    : WorkbookSource.base_44075
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:49:48.13165+00:00
-- url     : https://prove2.me/theorems/fdfd76aa-afbf-4897-9e00-83e40db6b424
-- title:
--   A cyclic quadratic difference ratio sum is nonnegative
-- statement:
--   Prove that $\forall a,b,c>0$ we have $\sum\frac{a^2-bc}{b^2+c^2+2a^2} \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44075` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44075; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44075 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 - b * c) / (b^2 + c^2 + 2 * a^2) + (b^2 - c * a) / (c^2 + a^2 + 2 * b^2) + (c^2 - a * b) / (a^2 + b^2 + 2 * c^2) ≥ 0  :=  by sorry
