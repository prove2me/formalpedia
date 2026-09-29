-- Prove2me | Theorems.Thm_lean_workbook_plus_65726
-- name    : lean_workbook_plus_65726
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b26677bc-5196-46ac-976d-0f8f74ea45a2
-- statement:
--   Find the remainder when $(8*3628800+1)(4*3628800+1)(2*3628800+1)(1*3628800+1)$ is divided by $210$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65726 : (8*3628800+1)*(4*3628800+1)*(2*3628800+1)*(1*3628800+1) % 210 = 1   :=  by sorry
