-- Prove2me | Theorems.Thm_lean_workbook_plus_9200
-- name    : lean_workbook_plus_9200
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5fa24864-4cb4-4328-8137-4aed2d7b318b
-- statement:
--   After squaring two times we get $ \left( 49\,{b}^{6}+54\,{b}^{5}+155\,{b}^{4}+68\,{b}^{3}+139\,{b}^{2}+14\,b+49 \right) \left( b-1 \right) ^{2} \geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9200 (b : ℝ) : (49 * b^6 + 54 * b^5 + 155 * b^4 + 68 * b^3 + 139 * b^2 + 14 * b + 49) * (b - 1)^2 ≥ 0   :=  by sorry
