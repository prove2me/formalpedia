-- Prove2me | Theorems.Thm_lean_workbook_plus_4637
-- name    : lean_workbook_plus_4637
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/2f6b15f4-7075-42d4-a752-a73db775e2c3
-- statement:
--   $ = -\frac{1}{2}\left(\cos{1^2}- \cos{0^2}\right) = \dfrac{1 - \cos{1}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4637 :
  -(1 / 2) * (Real.cos 1 - Real.cos 0) = (1 - Real.cos 1) / 2   :=  by sorry
