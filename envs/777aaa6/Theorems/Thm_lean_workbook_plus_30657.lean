-- Prove2me | Theorems.Thm_lean_workbook_plus_30657
-- name    : lean_workbook_plus_30657
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f0627935-3a50-43fe-ba8a-17da7388e6c8
-- statement:
--   The inequality $\Delta = (5 - c)^2 - 4(3 - 5c + c^2) \geq 0$ simplifies to $-3(c + 1)(c - \frac{13}{3}) \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30657 : ∀ c : ℝ, (5 - c) ^ 2 - 4 * (3 - 5 * c + c ^ 2) ≥ 0 ↔ -3 * (c + 1) * (c - 13 / 3) ≥ 0   :=  by sorry
