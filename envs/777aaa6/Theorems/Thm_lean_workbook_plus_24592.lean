-- Prove2me | Theorems.Thm_lean_workbook_plus_24592
-- name    : lean_workbook_plus_24592
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1a361259-9ccf-4830-a195-7cbd5f7dc201
-- statement:
--   Consider two real numbers $ x,y $ such that $ xy=6 $ and $ x,y>2. $ Show that $ x+y<5. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24592 (x y : ℝ) (h₁ : x * y = 6) (h₂ : 2 < x) (h₃ : 2 < y) : x + y < 5   :=  by sorry
