-- Prove2me | Theorems.Thm_lean_workbook_plus_13010
-- name    : lean_workbook_plus_13010
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4bceb8b5-ac68-410c-98e2-ed664ff5463c
-- statement:
--   Prove that $\frac{ab+c}{ab+2c+3}+\frac{bc+a}{bc+2a+3}+\frac{ac+b}{ac+2b+3}\leq \frac{a+b+c+3}{6}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13010 : ∀ a b c : ℝ, (a * b + c) / (a * b + 2 * c + 3) + (b * c + a) / (b * c + 2 * a + 3) + (c * a + b) / (c * a + 2 * b + 3) ≤ (a + b + c + 3) / 6   :=  by sorry
