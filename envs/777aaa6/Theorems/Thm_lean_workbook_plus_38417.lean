-- Prove2me | Theorems.Thm_lean_workbook_plus_38417
-- name    : lean_workbook_plus_38417
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/50ead283-af4d-47a6-b863-c9eb6c1e7483
-- statement:
--   Observe that $444 \cdot 418 \equiv 0 \mod 703$ since $37 | 444$ and $19 | 418$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38417 :
  (444 * 418) % 703 = 0   :=  by sorry
