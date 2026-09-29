-- Prove2me | Theorems.Thm_lean_workbook_plus_69024
-- name    : lean_workbook_plus_69024
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/f3cf00e6-a939-48ee-aed3-4c0a9f25cf63
-- statement:
--   Prove that if $ x^3 + y^3 + z^3 = 81$ with $ x,y,z > 0$ , then $ x + y + z\leq 9$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69024 (x y z : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) (h : x^3 + y^3 + z^3 = 81) : x + y + z ≤ 9   :=  by sorry
