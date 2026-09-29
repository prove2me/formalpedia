-- Prove2me | Theorems.Thm_lean_workbook_plus_61400
-- name    : lean_workbook_plus_61400
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f50068b3-3907-4d1b-9103-4659789c7b24
-- statement:
--   If $a\geqq b\geqq c, x\geqq y\geqq z, x+y+z=0$ , prove that we have $ax+by+cz\geqq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61400 (a b c x y z : ℝ) (h1 : a ≥ b ∧ b ≥ c) (h2 : x ≥ y ∧ y ≥ z) (h3 : x + y + z = 0) : a * x + b * y + c * z ≥ 0   :=  by sorry
