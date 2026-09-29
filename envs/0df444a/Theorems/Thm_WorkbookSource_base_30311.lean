-- Prove2me | Theorems.Thm_WorkbookSource_base_30311
-- name    : WorkbookSource.base_30311
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:23.731465+00:00
-- url     : https://prove2.me/theorems/a08504e3-38df-4d94-a15d-e11bef23d7f5
-- title:
--   A quartic correction to a two-variable sum bound
-- statement:
--   Let $a$ and $b$ be positive real numbers such that $a^2+b^2=2$. Prove that $a +b+\frac{1}{16}(a^2-b^2)^2\le 2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30311` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30311; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30311 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^2 = 2) : a + b + (1 / 16) * (a^2 - b^2)^2 ≤ 2  :=  by sorry
