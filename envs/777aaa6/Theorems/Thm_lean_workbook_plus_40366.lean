-- Prove2me | Theorems.Thm_lean_workbook_plus_40366
-- name    : lean_workbook_plus_40366
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/902d242d-de42-42cb-8080-b8e84cd03a82
-- statement:
--   What is the correct AM-GM solution to the inequality $(a^2+b^2)(c^2+d^2) \geq (ac+bd)^2$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40366 (a b c d : ℝ) : (a^2 + b^2) * (c^2 + d^2) ≥ (a * c + b * d)^2   :=  by sorry
