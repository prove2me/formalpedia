-- Prove2me | Theorems.Thm_WorkbookSource_base_815
-- name    : WorkbookSource.base_815
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:10:46.501847+00:00
-- url     : https://prove2.me/theorems/493ca736-75f6-47cf-b032-f837ac5e7fe0
-- title:
--   A quadratic relation bounds a sum minus product
-- statement:
--   Let $a,b\geq 0$ and $ a^2+b^2=a+b.$ Prove that
--
--    $$ a+ b- ab\leq \frac{9}{8} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_815` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_815; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_815 (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hab : a^2 + b^2 = a + b) : a + b - a * b ≤ 9 / 8  :=  by sorry
