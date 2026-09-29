-- Prove2me | Theorems.Thm_lean_workbook_plus_62981
-- name    : lean_workbook_plus_62981
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/443cf493-c657-437e-be79-4e8598ce2beb
-- statement:
--   Prove that for all real numbers $ x,y$ excluding 0: $ x^2 + xy + y^2 > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62981 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : x ^ 2 + x * y + y ^ 2 > 0   :=  by sorry
