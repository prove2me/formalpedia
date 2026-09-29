-- Prove2me | Theorems.Thm_lean_workbook_plus_37346
-- name    : lean_workbook_plus_37346
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/258b5808-93c0-4baa-ada0-df2e5b263624
-- statement:
--   If $x,y,z$ are reals and $x+y+z=5$ and $xy+yz+zx=3$ prove that $-1\leq z\leq\frac{13}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37346 (x y z : ℝ) (h₁ : x + y + z = 5) (h₂ : x * y + y * z + z * x = 3) : -1 ≤ z ∧ z ≤ 13 / 3   :=  by sorry
