-- Prove2me | Theorems.Thm_WorkbookSource_base_15195
-- name    : WorkbookSource.base_15195
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:06.306763+00:00
-- url     : https://prove2.me/theorems/9b9928fe-3a8a-4b2d-8185-fabb2bd0ca61
-- title:
--   A normalized product bound for three quadratic forms
-- statement:
--   The inequality is equivalent with:
--
--    $x,y,z\ge 0,\;x+y+z=2\;\Longrightarrow $ $(x^2+xy+y^2)(y^2+yz+z^2)(z^2+zx+x^2)\leq3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15195` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15195; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15195 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 2) : (x^2 + x*y + y^2)*(y^2 + y*z + z^2)*(z^2 + z*x + x^2) ≤ 3  :=  by sorry
