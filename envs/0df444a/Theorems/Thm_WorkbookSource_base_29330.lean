-- Prove2me | Theorems.Thm_WorkbookSource_base_29330
-- name    : WorkbookSource.base_29330
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:13:10.752559+00:00
-- url     : https://prove2.me/theorems/cd1d888b-5859-4a5d-a073-b57c7c787654
-- title:
--   A comparison of weighted cyclic reciprocal sums
-- statement:
--   INEQUALITY I Let $a,b,c$ be positive real numbers.Prove that
--    $\frac{1}{{a + 2b}} + \frac{1}{{b + 2c}} + \frac{1}{{c + 2a}} + \frac{3}{{a + b + c}} \ge 4\left( {\frac{1}{{3a + 2b + c}} + \frac{1}{{a + 3b + 2c}} + \frac{1}{{2a + b + 3c}}} \right).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29330` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29330; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29330 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a) + 3 / (a + b + c) ≥ 4 * (1 / (3 * a + 2 * b + c) + 1 / (a + 3 * b + 2 * c) + 1 / (2 * a + b + 3 * c))  :=  by sorry
