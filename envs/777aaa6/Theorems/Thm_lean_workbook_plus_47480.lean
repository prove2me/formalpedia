-- Prove2me | Theorems.Thm_lean_workbook_plus_47480
-- name    : lean_workbook_plus_47480
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4d494c95-8748-4e75-8600-5c20be3004c5
-- statement:
--   Adding the two inequalities $0<x-xy$ and $0<xy$ gives $0<xy+x-xy$ which simplifies to $0<x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47480 : ∀ x y : ℝ, 0 < x - xy ∧ 0 < xy → 0 < x   :=  by sorry
