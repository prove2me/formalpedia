-- Prove2me | Theorems.Thm_WorkbookSource_base_44986
-- name    : WorkbookSource.base_44986
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:07.049975+00:00
-- url     : https://prove2.me/theorems/8315aaf1-5cbd-437c-9e5f-154f485bca2c
-- title:
--   A cyclic quartic upper bound on a sphere
-- statement:
--   Using Vasile's inequality, prove that for $x, y, z \in \mathbb{R}$ and $x^2 + y^2 + z^2 = 3$, $x^3y + y^3z + z^3x \leq 3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44986` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44986; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44986 (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
  x ^ 3 * y + y ^ 3 * z + z ^ 3 * x ≤ 3  :=  by sorry
