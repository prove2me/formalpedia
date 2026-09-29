-- Prove2me | Theorems.Thm_lean_workbook_plus_76739
-- name    : lean_workbook_plus_76739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d83f46f9-6e6b-40cb-8cd0-c39cb3dddc17
-- statement:
--   If $a,b,c \in R$ ,then $\left( {a + b} \right)^2 \left( {b + c} \right)^2 \left( {c + a} \right)^2 - 4\left( {a^2 + bc} \right)\left( {b^2 + ca} \right)\left( {c^2 + ab} \right) - 4abc\left( {a + b} \right)\left( {b + c} \right)\left( {c + a} \right) = \left( {a - b} \right)^2 \left( {b - c} \right)^2 \left( {c - a} \right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76739 {a b c : ℝ} :
  (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 - 4 * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) - 4 * a * b * c * (a + b) * (b + c) * (c + a) =
  (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2   :=  by sorry
