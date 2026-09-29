-- Prove2me | Theorems.Thm_lean_workbook_plus_2320
-- name    : lean_workbook_plus_2320
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8b7c8e57-9c08-4783-a826-96094f6798eb
-- statement:
--   Also, $2^{14} - 2^{10}$ can be quickly computed via difference-of-squares. $$\left(2^{7}\right)^2 - \left(2^{5}\right)^2 = (128 + 32)(128 - 32) = (160)(96) = \boxed{15360}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2320 :
  (2^14 - 2^10) = 15360   :=  by sorry
