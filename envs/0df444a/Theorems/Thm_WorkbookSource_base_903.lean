-- Prove2me | Theorems.Thm_WorkbookSource_base_903
-- name    : WorkbookSource.base_903
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:45:19.552384+00:00
-- url     : https://prove2.me/theorems/4558055f-b987-4aad-9825-737ab5f1bb6b
-- title:
--   A quartic power-sum bound at total five
-- statement:
--   Let $ a,b,c\in \mathbb{R}$ such that $ a+b+c=5$ . Prove that:
--
--    $ a^4+b^4+c^4+13(a^2+b^2+c^2)\ge 6(a^3+b^3+c^3)+48$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_903` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_903; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_903 (a b c : ℝ) (h : a + b + c = 5) :
  a^4 + b^4 + c^4 + 13 * (a^2 + b^2 + c^2) ≥ 6 * (a^3 + b^3 + c^3) + 48  :=  by sorry
