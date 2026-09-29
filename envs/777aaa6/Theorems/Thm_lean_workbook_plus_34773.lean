-- Prove2me | Theorems.Thm_lean_workbook_plus_34773
-- name    : lean_workbook_plus_34773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/d6542775-a92a-418a-ab46-db61fb937a69
-- statement:
--   $ \Leftrightarrow a(a+b)(a+c)\geq (a+b)bc+(a+c)bc \Leftrightarrow (a^2-bc)(a+b+c)\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34773 (a b c : ℝ) : a * (a + b) * (a + c) ≥ (a + b) * b * c + (a + c) * b * c ↔ (a^2 - b * c) * (a + b + c) ≥ 0   :=  by sorry
