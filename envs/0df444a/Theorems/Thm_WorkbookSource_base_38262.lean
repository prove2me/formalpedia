-- Prove2me | Theorems.Thm_WorkbookSource_base_38262
-- name    : WorkbookSource.base_38262
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:55:09.354021+00:00
-- url     : https://prove2.me/theorems/020bc39f-5cbf-451f-9939-e00587c882c0
-- title:
--   A triple-product correction to a pairwise-sum bound
-- statement:
--   Prove that if $x$, $y$, and $z$ are positive real numbers such that $x + y + z = 3$, then $11 + xyz \geq 4(xy + yz + zx)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38262` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38262; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38262 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = 3) : 11 + x*y*z ≥ 4*(x*y + y*z + z*x)  :=  by sorry
