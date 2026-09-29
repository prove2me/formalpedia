-- Prove2me | Theorems.Thm_lean_workbook_plus_52855
-- name    : lean_workbook_plus_52855
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/732e29a0-e157-45b5-a263-6dc9b2ac03cf
-- statement:
--   $\sin(\alpha)\sin(x) = \sin(y) - \sin(x)\sin(y)\cos(\alpha)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52855 : ∀ α x y : ℝ, sin α * sin x = sin y - sin x * sin y * cos α   :=  by sorry
