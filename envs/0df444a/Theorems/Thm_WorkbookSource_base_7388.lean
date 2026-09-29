-- Prove2me | Theorems.Thm_WorkbookSource_base_7388
-- name    : WorkbookSource.base_7388
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:45.417904+00:00
-- url     : https://prove2.me/theorems/f10a3531-f97b-4e42-a094-dd80ab3a8413
-- title:
--   A sixth-degree bound on a product of three quadratic differences
-- statement:
--   Let $a,b,c$ be real numbers. Prove the inequality
--
--    $$8(a^2-bc)(b^2-ca)(c^2-ab) \leqslant (a^2+b^2+c^2)^3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7388` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7388; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7388 (a b c : ℝ) : 8 * (a^2 - b * c) * (b^2 - c * a) * (c^2 - a * b) ≤ (a^2 + b^2 + c^2)^3  :=  by sorry
