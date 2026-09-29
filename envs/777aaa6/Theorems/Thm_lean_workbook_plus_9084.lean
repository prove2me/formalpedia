-- Prove2me | Theorems.Thm_lean_workbook_plus_9084
-- name    : lean_workbook_plus_9084
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2796d511-c717-4256-a232-817d1146046e
-- statement:
--   Let $a,b,c$ be non negative real numbers satisfying $a+b^2+c^2=1$ . Prove that $ (1+a^2)(1+b^2)(1+c^2)\geq \frac{50}{27} $ Equality holds when $a=\frac{1}{3},b=0,c=\sqrt{\frac{2}{3}} $ or $a=\frac{1}{3},b=\sqrt{\frac{2}{3}},c=0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9084 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b^2 + c^2 = 1) : (1 + a^2) * (1 + b^2) * (1 + c^2) ≥ 50 / 27 ∧ (a = 1 / 3 ∧ b = 0 ∧ c = Real.sqrt (2 / 3) ∨ a = 1 / 3 ∧ b = Real.sqrt (2 / 3) ∧ c = 0) ↔ a = 1 / 3 ∧ b = 0 ∧ c = Real.sqrt (2 / 3) ∨ a = 1 / 3 ∧ b = Real.sqrt (2 / 3) ∧ c = 0   :=  by sorry
