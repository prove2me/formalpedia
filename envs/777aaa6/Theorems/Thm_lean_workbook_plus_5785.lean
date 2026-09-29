-- Prove2me | Theorems.Thm_lean_workbook_plus_5785
-- name    : lean_workbook_plus_5785
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/61c1dd1c-7463-4541-8bc0-c6749c337983
-- statement:
--   $ a\leq b \implies a\leq b + e$ , $ \forall e > 0$ , but not in reverse way
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5785 : a ≤ b → ∀ ε : ℝ, ε > 0 → a ≤ b + ε   :=  by sorry
