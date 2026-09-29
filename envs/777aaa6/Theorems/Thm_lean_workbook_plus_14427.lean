-- Prove2me | Theorems.Thm_lean_workbook_plus_14427
-- name    : lean_workbook_plus_14427
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4220ea34-41d9-459b-9292-af5d408c5b7e
-- statement:
--   The fraction equals $(n+1)(n+2)-(n+1)=(n+1)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14427  (n : ℕ)
  (h₀ : 0 < n) :
  ((n + 1) * (n + 2) - (n + 1)) = (n + 1)^2   :=  by sorry
