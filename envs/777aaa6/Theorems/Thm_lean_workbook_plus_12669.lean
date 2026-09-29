-- Prove2me | Theorems.Thm_lean_workbook_plus_12669
-- name    : lean_workbook_plus_12669
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/31c6bfaa-2320-4624-b3d9-8e8f3634566d
-- statement:
--   Solve the system of equations\n$x+y+z=\pi$\n$\tan x\tan z=2$\n$\tan y\tan z=18$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12669 (x y z : ℝ) (hx : x + y + z = π) (hxy : tan x * tan z = 2) (hzy : tan y * tan z = 18) : x = π/3 ∧ y = π/3 ∧ z = π/3   :=  by sorry
