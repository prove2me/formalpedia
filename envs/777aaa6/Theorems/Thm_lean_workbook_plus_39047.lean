-- Prove2me | Theorems.Thm_lean_workbook_plus_39047
-- name    : lean_workbook_plus_39047
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6a2059d6-e095-415a-8775-05f530b37fc7
-- statement:
--   Prove the cosine difference formula: $\cos(x-y) = \cos(x)\cos(y) + \sin(x)\sin(y)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39047 (x y : ℝ) : cos (x - y) = cos x * cos y + sin x * sin y   :=  by sorry
