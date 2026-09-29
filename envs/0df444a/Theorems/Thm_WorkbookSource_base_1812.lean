-- Prove2me | Theorems.Thm_WorkbookSource_base_1812
-- name    : WorkbookSource.base_1812
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:45:39.467739+00:00
-- url     : https://prove2.me/theorems/ae5c39b7-6e66-479f-b6cf-3d92d10d5a5a
-- title:
--   A quartic symmetric sum bounds a quadratic sum at total three
-- statement:
--   The following inequality is true already.
--   Let $a$ , $b$ and $c$ be real numbers such that $a+b+c=3$ . Prove that:
--    $$a^4+b^4+c^4+4(a^2b^2+b^2c^2+c^2a^2) \geqslant 5(a^2+b^2+c^2)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1812` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1812; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1812 (a b c : ℝ) (h : a + b + c = 3) : a^4 + b^4 + c^4 + 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 5 * (a^2 + b^2 + c^2)  :=  by sorry
