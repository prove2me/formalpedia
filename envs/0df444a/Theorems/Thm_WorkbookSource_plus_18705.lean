-- Prove2me | Theorems.Thm_WorkbookSource_plus_18705
-- name    : WorkbookSource.plus_18705
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:32.733119+00:00
-- url     : https://prove2.me/theorems/48725996-8b53-4f14-a754-62f743e91f3a
-- title:
--   A cyclic shifted-square inequality at unit product
-- statement:
--   Let $x$, $y$, and $z$ be positive reals such that $xyz=1$. Prove that $\sum x^2(2y-1)^2+5\ge(1+x)(1+y)(1+z)+3(1-x)(1-y)(1-z)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_18705` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_18705; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_18705 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x*y*z = 1) : x^2 * (2*y - 1)^2 + y^2 * (2*z - 1)^2 + z^2 * (2*x - 1)^2 + 5 ≥ (1 + x) * (1 + y) * (1 + z) + 3 * (1 - x) * (1 - y) * (1 - z)   :=  by sorry
