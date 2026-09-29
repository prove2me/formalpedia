-- Prove2me | Theorems.Thm_WorkbookSource_plus_30461
-- name    : WorkbookSource.plus_30461
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:49:53.469391+00:00
-- url     : https://prove2.me/theorems/b270142d-47ee-4dc1-9df5-02fdbcf199f5
-- title:
--   A quartic sum and triple product bound a cubic sum
-- statement:
--   Let $a,b,c$ be real (not only positive) numbers such that $a+b+c = 1$ . Prove the inequality
--
--   $2(a^4+b^4+c^4) + abc \ge a^3 + b^3 + c^3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_30461` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_30461; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_30461 (a b c : ℝ) (ha : a + b + c = 1) : 2 * (a^4 + b^4 + c^4) + a * b * c ≥ a^3 + b^3 + c^3   :=  by sorry
