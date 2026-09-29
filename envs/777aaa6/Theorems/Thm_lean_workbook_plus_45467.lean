-- Prove2me | Theorems.Thm_lean_workbook_plus_45467
-- name    : lean_workbook_plus_45467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7aa70f80-0a9b-45a0-8e5e-b308ad528816
-- statement:
--   Let $ a,b,c >0$ s.t $ ab+bc+ac+2abc=1$ .Prove that $ \frac{1}{a+b+2}+\frac{1}{c+b+2}+\frac{1}{a+c+2} \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45467 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a + 2 * a * b * c = 1) : 1 / (a + b + 2) + 1 / (b + c + 2) + 1 / (c + a + 2) ≤ 1   :=  by sorry
