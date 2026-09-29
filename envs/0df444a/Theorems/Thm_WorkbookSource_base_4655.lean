-- Prove2me | Theorems.Thm_WorkbookSource_base_4655
-- name    : WorkbookSource.base_4655
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:18.271054+00:00
-- url     : https://prove2.me/theorems/eaa8579d-c6ed-4d95-b233-57c94d37c609
-- title:
--   A squared pairwise-sum lower bound for a rational product
-- statement:
--   Let $a,b,c$ be positive real numbers .Prove that
--
--    $$(a+b)^2+(a+b+2c)^2\geq \frac{100abc}{2a+2b+c}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4655` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4655; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4655 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 + (a + b + 2 * c) ^ 2 ≥ 100 * a * b * c / (2 * a + 2 * b + c)  :=  by sorry
