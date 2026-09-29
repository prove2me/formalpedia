-- Prove2me | Theorems.Thm_lean_workbook_plus_57250
-- name    : lean_workbook_plus_57250
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/7966e95f-5199-441f-8758-7ec9fa3e4178
-- statement:
--   we have $(\forall a\le \frac{4}{3}):\frac{(3a-4)(3a-1)^2}{50(1+a^2)}\le0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57250 : ∀ a ≤ (4:ℝ) / 3, (3 * a - 4) * (3 * a - 1) ^ 2 / (50 * (1 + a ^ 2)) ≤ 0   :=  by sorry
