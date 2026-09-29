-- Prove2me | Theorems.Thm_WorkbookSource_base_51926
-- name    : WorkbookSource.base_51926
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:40.56769+00:00
-- url     : https://prove2.me/theorems/18a55ffb-f4ba-4ad3-af2b-628f2eb16210
-- title:
--   A parameterized quadratic inequality in three variables
-- statement:
--   Let $a,b,c$ be real numbers. Prove that
--    $$a^2+b^2+c^2+ka+\frac{k^2}{3}\ge ab+bc+ca+kc$$ Where $ k\in R.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51926` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51926; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_51926 (a b c k : ℝ): a^2 + b^2 + c^2 + k*a + k^2 / 3 ≥ a * b + b * c + c * a + k * c  :=  by sorry
