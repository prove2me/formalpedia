-- Prove2me | Theorems.Thm_lean_workbook_plus_77372
-- name    : lean_workbook_plus_77372
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0fd95829-3edb-4146-8136-15f5e3a2cd1c
-- statement:
--   Prove the inequality: $\frac{1}{a^2}+\frac{1}{b^2}+\frac{1}{c^2} \geq \frac{1}{ab}+\frac{1}{bc}+\frac{1}{ca}$, where $a^2 = \sqrt{x+y}$, $b^2 = \sqrt{y+z}$, and $c^2 = \sqrt{x+z}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77372 (x y z a b c : ℝ) (ha : a^2 = Real.sqrt (x + y)) (hb : b^2 = Real.sqrt (y + z)) (hc : c^2 = Real.sqrt (x + z)) : 1 / a^2 + 1 / b^2 + 1 / c^2 ≥ 1 / (a * b) + 1 / (b * c) + 1 / (c * a)   :=  by sorry
