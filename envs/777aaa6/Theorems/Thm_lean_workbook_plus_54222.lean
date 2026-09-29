-- Prove2me | Theorems.Thm_lean_workbook_plus_54222
-- name    : lean_workbook_plus_54222
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/87afcd65-4708-46b1-ad91-416dc1505926
-- statement:
--   Prove that for all polynomials f and g, $\deg (fg)=\deg f + \deg g$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54222 (f g : Polynomial ℤ) : (f * g).degree = f.degree + g.degree   :=  by sorry
