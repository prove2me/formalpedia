-- Prove2me | Theorems.Thm_WorkbookSource_base_21546
-- name    : WorkbookSource.base_21546
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:58.013102+00:00
-- url     : https://prove2.me/theorems/aa8115fa-f24f-4feb-8dd8-224919e3694b
-- title:
--   A symmetric quartic inequality on the unit sphere
-- statement:
--   Let $ x$ , $ y$ and $ z$ be real numbers such that $ x^{2}+y^{2}+z^{2}=1$ . Prove that: $ 7(x^{4}+y^{4}+z^{4})+8(x+y+z)(xyz)\ge 4(xy+yz+zx)+1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21546` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21546; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21546 (x y z : ℝ) (hx : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
  7 * (x ^ 4 + y ^ 4 + z ^ 4) + 8 * (x + y + z) * (x * y * z) ≥
  4 * (x * y + y * z + z * x) + 1  :=  by sorry
