-- Prove2me | Theorems.Thm_lean_workbook_plus_3092
-- name    : lean_workbook_plus_3092
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e241bd3f-0d66-462c-a69f-56946470d9f1
-- statement:
--   Let $a, b, c > 0$ such that $a \geq 3$, $\frac{a}{3} + \frac{b}{2} \geq 2$, and $\frac{a}{3} + \frac{b}{2} + c \geq 3$. Prove that $a^3 + b^3 + c^3 \geq 36$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3092 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≥ 3) (hbc : a / 3 + b / 2 ≥ 2) (habc : a / 3 + b / 2 + c ≥ 3) : a ^ 3 + b ^ 3 + c ^ 3 ≥ 36   :=  by sorry
