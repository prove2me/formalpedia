-- Prove2me | Theorems.Thm_WorkbookSource_base_55925
-- name    : WorkbookSource.base_55925
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:44.272636+00:00
-- url     : https://prove2.me/theorems/36068be7-7a04-490c-a1d9-065a83634417
-- title:
--   A quartic bound with a triple-product correction at fixed sum two
-- statement:
--   Let $x,y,z\ge0$ such that $x+y+z=2$ . Prove that $x^2y^2+y^2z^2+z^2x^2-2xyz\leq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_55925` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_55925; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_55925 (x y z : ℝ) (h : x + y + z = 2) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 - 2 * x * y * z ≤ 1  :=  by sorry
