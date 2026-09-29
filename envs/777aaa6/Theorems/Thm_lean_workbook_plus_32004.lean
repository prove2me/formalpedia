-- Prove2me | Theorems.Thm_lean_workbook_plus_32004
-- name    : lean_workbook_plus_32004
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/02098296-bdc2-4890-bff9-991905be47e1
-- statement:
--   Without using a calculator or approximations like $\sqrt{2} \approx 1.414$ or $\sqrt{3} \approx 1.732$, prove that $2\sqrt{3}-2 > \sqrt{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32004 : (2 * Real.sqrt 3 - 2) > Real.sqrt 2   :=  by sorry
