-- Prove2me | Theorems.Thm_lean_workbook_plus_82579
-- name    : lean_workbook_plus_82579
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7711be89-2057-4da2-a57e-5d8f40c0957f
-- statement:
--   Let $a+b = z, b+c = x, c+a = y=>a=\frac{y+z-x}{2},b=\frac{z+x-y}{2},c=\frac{x+y-z}{2}$ .where $x,y,z>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82579 (x y z a b c : ℝ) : x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y → a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2   :=  by sorry
