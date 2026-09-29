-- Prove2me | Theorems.Thm_lean_workbook_plus_81739
-- name    : lean_workbook_plus_81739
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/95ed70e1-62f9-48f4-8021-5a4c5d85b340
-- statement:
--   prove that: $a^5 + b^5 + c^5 + 2 \geq 5abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81739 ∀ a b c: ℝ, a^5 + b^5 + c^5 + 2 ≥ 5 * a * b * c   :=  by sorry
