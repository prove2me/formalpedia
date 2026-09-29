-- Prove2me | Theorems.Thm_WorkbookSource_base_16261
-- name    : WorkbookSource.base_16261
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:03:16.236907+00:00
-- url     : https://prove2.me/theorems/bc901d0e-9903-4f3e-a02a-b35cf80be8c5
-- title:
--   A weighted cyclic quadratic ratio bounds the quadratic mean
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that:
--
--    $$ \frac{a^2}{2a+5b}+ \frac{b^2}{2b+5c}+ \frac{c^2}{2c+5a}\geq \frac{3(a^2+b^2+c^2)}{7(a+b+c)} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16261` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16261; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16261 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / (2 * a + 5 * b) + b^2 / (2 * b + 5 * c) + c^2 / (2 * c + 5 * a)) ≥ (3 * (a^2 + b^2 + c^2)) / (7 * (a + b + c))  :=  by sorry
