-- Prove2me | Theorems.Thm_WorkbookSource_base_38274
-- name    : WorkbookSource.base_38274
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:40.309757+00:00
-- url     : https://prove2.me/theorems/ca11797c-0058-4fec-a608-524d064cc459
-- title:
--   A symmetric cubic bound under a quadratic norm constraint
-- statement:
--   Let three non-negative reals $ x,y,z $ satisfy : $ x^2+y^2+z^2=2 $ . Prove that : $$(x+y+z+2)(xy+yz+zx)-9xyz \le 4$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38274` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38274; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38274 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x^2 + y^2 + z^2 = 2) :
  (x + y + z + 2) * (x * y + y * z + z * x) - 9 * x * y * z ≤ 4  :=  by sorry
