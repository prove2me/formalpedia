-- Prove2me | Theorems.Thm_lean_workbook_plus_68905
-- name    : lean_workbook_plus_68905
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/68e9f96e-9fef-4e57-8f96-48af87cbcfaa
-- statement:
--   $WLOG$ , assume that $a \geq b \geq c > 0$ . Then we have : \n\n $i)$ $\frac{a^2}{b^2+c^2} \geq \frac{b^2}{c^2+a^2} \geq \frac{c^2}{a^2+b^2}$ \n\n $ii)$ $\frac{b+c}{2a+b+c} \leq \frac{c+a}{2b+c+a} \leq \frac{a+b}{2c+a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68905 (a b c : ℝ) (h : a >= b ∧ b >= c ∧ c > 0) :
  a^2 / (b^2 + c^2) >= b^2 / (c^2 + a^2) ∧ b^2 / (c^2 + a^2) >= c^2 / (a^2 + b^2)   :=  by sorry
