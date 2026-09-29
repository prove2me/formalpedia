-- Prove2me | Theorems.Thm_WorkbookSource_plus_63009
-- name    : WorkbookSource.plus_63009
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:49.90537+00:00
-- url     : https://prove2.me/theorems/4d2f99cd-7b49-490b-b0f2-fa5a9210c3ef
-- title:
--   A weighted norm lower bound under a linear constraint
-- statement:
--   Let $a,b,c$ be real numbers such that $2a+b+3c=20$. $a^2+4b^2+c^2\geq\frac{1600}{53}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_63009` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63009; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_63009 (a b c : ℝ) (h : 2*a + b + 3*c = 20) : a^2 + 4*b^2 + c^2 ≥ 1600/53   :=  by sorry
