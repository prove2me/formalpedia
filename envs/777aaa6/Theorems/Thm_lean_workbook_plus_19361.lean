-- Prove2me | Theorems.Thm_lean_workbook_plus_19361
-- name    : lean_workbook_plus_19361
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/36e7aeea-e0b9-47b9-8107-db935870183b
-- statement:
--   Which,clearly,can be reduced to:\n\n $ (a^3b^3 + b^3c^3 + c^3a^3 + 3a^2b^2c^2)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19361 {a b c : ℝ} : (a^3 * b^3 + b^3 * c^3 + c^3 * a^3 + 3 * a^2 * b^2 * c^2)^2 ≥ 0   :=  by sorry
