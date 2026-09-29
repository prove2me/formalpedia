-- Prove2me | Theorems.Thm_lean_workbook_plus_6576
-- name    : lean_workbook_plus_6576
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/b6252c6d-e6a1-4843-ab86-00dbbb999c2c
-- statement:
--   Given that $307^2$ divides $a$, find the remainder when $a$ is divided by $307^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6576 (a : ℕ) (h : 307^2 ∣ a) : a % 307^2 = 0   :=  by sorry
