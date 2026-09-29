-- Prove2me | Theorems.Thm_lean_workbook_plus_55030
-- name    : lean_workbook_plus_55030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/86ac2578-5c91-4bc9-b350-fd61c820ba42
-- statement:
--   Prove $3(x^2 +xy+y^2) \ge \frac{9}{4} (x+y)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55030 : ∀ x y : ℝ, 3 * (x ^ 2 + x * y + y ^ 2) ≥ (9 / 4) * (x + y) ^ 2   :=  by sorry
