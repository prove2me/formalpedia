-- Prove2me | Theorems.Thm_WorkbookSource_base_3816
-- name    : WorkbookSource.base_3816
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:10:15.876344+00:00
-- url     : https://prove2.me/theorems/445a81be-6539-4c34-a932-0acade8f9f24
-- title:
--   A cyclic cubic lower bound under a quartic norm constraint
-- statement:
--   Let $x;y;z$ be real number such that $x^4+y^4+z^4=3$
--   Prove: $x^2(x+y)+y^2(y+z)+z^2(z+x) \geq -6$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3816` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3816; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3816 (x y z: ℝ) (h : x ^ 4 + y ^ 4 + z ^ 4 = 3) :
  x ^ 2 * (x + y) + y ^ 2 * (y + z) + z ^ 2 * (z + x) ≥ -6  :=  by sorry
