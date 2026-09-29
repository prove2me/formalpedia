-- Prove2me | Theorems.Thm_WorkbookSource_base_18675
-- name    : WorkbookSource.base_18675
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:23:20.718408+00:00
-- url     : https://prove2.me/theorems/ffa43c32-f10b-42a9-8a09-609b3857975e
-- title:
--   A cyclic quintic bound under a cubic sum-product relation
-- statement:
--   Let $a,b,c$ be positive reals satisfying $a+b+c=abc.$
--   $ \sum a(1-b^2)(1-c^2) \leq \frac{4}{27}(a+b+c)^3 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18675` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18675; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18675 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = a * b * c) : a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - c ^ 2) * (1 - a ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2) ≤ (4 / 27) * (a + b + c) ^ 3  :=  by sorry
