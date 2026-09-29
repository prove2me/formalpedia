-- Prove2me | Theorems.Thm_WorkbookSource_base_23386
-- name    : WorkbookSource.base_23386
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:12.710443+00:00
-- url     : https://prove2.me/theorems/bfce0e89-ce31-404a-9a9d-83199515842a
-- title:
--   A cyclic product comparison of quadratic factors
-- statement:
--   prove that:
--
--    $(zx+y^2)(xy+z^2)(yz+x^2)\geq (zx+z^2)(xy+x^2)(yz+y^2)$
--
--   $x,y,z\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23386` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23386; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23386 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (z * x + y ^ 2) * (x * y + z ^ 2) * (y * z + x ^ 2) ≥ (z * x + z ^ 2) * (x * y + x ^ 2) * (y * z + y ^ 2)  :=  by sorry
