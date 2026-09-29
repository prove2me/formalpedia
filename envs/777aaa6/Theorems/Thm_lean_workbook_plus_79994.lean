-- Prove2me | Theorems.Thm_lean_workbook_plus_79994
-- name    : lean_workbook_plus_79994
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/85c52ea3-e668-460d-a5a7-b37b00bc7524
-- statement:
--   $ (z + 2)^2 = 0\Longrightarrow\fbox{z = - 2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79994  (z : ℂ)
  (h₀ : (z + 2)^2 = 0) :
  z = -2   :=  by sorry
