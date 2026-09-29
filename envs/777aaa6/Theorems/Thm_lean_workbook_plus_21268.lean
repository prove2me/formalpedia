-- Prove2me | Theorems.Thm_lean_workbook_plus_21268
-- name    : lean_workbook_plus_21268
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2f4120ea-4ab8-4b71-805b-1b48a0380c08
-- statement:
--   Prove that $ \frac {5}{2} < \sin ^ 4 \frac {\alpha}{4} + \cos ^ 4 \frac {\alpha}{4} + \sin ^ 4 \frac {\beta}{4} + \cos ^ 4 \frac {\beta}{4} + \sin ^ 4 \frac {\gamma}{4} + \cos ^ 4 \frac {\gamma}{4}\leq \frac {21}{8}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21268 : ∀ α β γ : ℝ, 5 / 2 < sin (α / 4) ^ 4 + cos (α / 4) ^ 4 + sin (β / 4) ^ 4 + cos (β / 4) ^ 4 + sin (γ / 4) ^ 4 + cos (γ / 4) ^ 4 ∧ sin (α / 4) ^ 4 + cos (α / 4) ^ 4 + sin (β / 4) ^ 4 + cos (β / 4) ^ 4 + sin (γ / 4) ^ 4 + cos (γ / 4) ^ 4 ≤ 21 / 8   :=  by sorry
