-- Prove2me | Theorems.Thm_lean_workbook_plus_8556
-- name    : lean_workbook_plus_8556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a7cf3eb8-29aa-4c8a-8367-e7f645d4acda
-- statement:
--   If $x^2+ax+b=0$ has an integral root $x_0$ not equal to 0, then show that $x_0|b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8556 (a b : ℤ) (x0 : ℤ) (hx0 : x0 ≠ 0) (h : x0^2 + a * x0 + b = 0) : x0 ∣ b   :=  by sorry
