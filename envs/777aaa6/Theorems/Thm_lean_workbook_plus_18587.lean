-- Prove2me | Theorems.Thm_lean_workbook_plus_18587
-- name    : lean_workbook_plus_18587
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/caf10b7c-8e74-4dc0-8d23-c8a1b241767a
-- statement:
--   Prove that $xy + yz + zx \le 2xyz + 1$ for $x,y,z > 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18587 (x y z : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) : x * y + y * z + z * x ≤ 2 * x * y * z + 1   :=  by sorry
