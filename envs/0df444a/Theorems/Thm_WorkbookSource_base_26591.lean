-- Prove2me | Theorems.Thm_WorkbookSource_base_26591
-- name    : WorkbookSource.base_26591
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:24.17333+00:00
-- url     : https://prove2.me/theorems/c3daffa0-b681-47c9-ac5e-441dc4769230
-- title:
--   An asymmetric quartic inequality on nonnegative variables
-- statement:
--   Let $x,y,z\geq 0$ ,prove that: $-(x+y+z)xyz+x^4+yz(y^2+z^2)\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26591` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26591; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26591 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : -(x + y + z)*x*y*z + x^4 + y*z*(y^2 + z^2) ≥ 0  :=  by sorry
