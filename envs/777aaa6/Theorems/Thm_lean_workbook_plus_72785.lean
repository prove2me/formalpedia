-- Prove2me | Theorems.Thm_lean_workbook_plus_72785
-- name    : lean_workbook_plus_72785
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/87b567fd-8190-4e28-b6dd-fec5078fa29b
-- statement:
--   The chances of both the card and the envelope of having the requested combination of colors is $2 \displaystyle(\frac{1}{42})(\frac{41}{42}) = \frac{41}{882}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72785 :
  ((1:ℝ) / 42 * (41:ℝ) / 42) * 2 = (41:ℝ) / 882   :=  by sorry
