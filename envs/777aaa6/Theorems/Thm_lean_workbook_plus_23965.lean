-- Prove2me | Theorems.Thm_lean_workbook_plus_23965
-- name    : lean_workbook_plus_23965
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3dbb630f-af09-41df-9c8c-6ae86f9f3c10
-- statement:
--   Let $(x,y,z)$ be real number with $x,y,z$ ≥ $-1$ and $x + y$ ≥ $2$ , $x + z$ ≥ $2$ , $y + z$ ≥ $2$ . Show that $xy + xz + yz$ ≥ $3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23965 (x y z : ℝ) (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) (hxy : x + y ≥ 2) (hxz : x + z ≥ 2) (hyz : y + z ≥ 2) : x * y + x * z + y * z ≥ 3   :=  by sorry
