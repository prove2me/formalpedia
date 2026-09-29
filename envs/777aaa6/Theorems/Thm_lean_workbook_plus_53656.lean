-- Prove2me | Theorems.Thm_lean_workbook_plus_53656
-- name    : lean_workbook_plus_53656
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/155e92d9-bb21-43f0-a0cb-ef6db5110aa2
-- statement:
--   Prove that $|\begin{ matrix } -2a & \quad \quad \quad \quad a+b & \quad \quad \quad \quad c+a \ a+b & \quad \quad -2b & \quad \quad \quad \quad b+c \ c+a & \quad \quad \quad \quad c+b & \quad \quad \quad \quad -2c \end{ matrix }|=\quad \quad 4(a+b)(b+c)(c+a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53656 (a b c : ℝ) : Matrix.det (![![-2*a, a+b, c+a],![a+b, -2*b, b+c],![c+a, b+c, -2*c]]) = 4*(a+b)*(b+c)*(c+a)   :=  by sorry
