-- Prove2me | Theorems.Thm_lean_workbook_plus_45426
-- name    : lean_workbook_plus_45426
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/a766b051-8c8b-46fb-872b-2c1400e3625e
-- statement:
--   Assume that real numbers $x$ , $y$ and $z$ satisfy $x + y + z = 3$ . Prove that $xy + xz + yz \leq 3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45426 (x y z : ℝ) (h : x + y + z = 3) : x*y + x*z + y*z ≤ 3   :=  by sorry
