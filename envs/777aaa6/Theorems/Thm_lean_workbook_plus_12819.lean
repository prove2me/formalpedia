-- Prove2me | Theorems.Thm_lean_workbook_plus_12819
-- name    : lean_workbook_plus_12819
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/29703528-190e-4444-89fa-1ab1ef10bac1
-- statement:
--   $0 \cdot 300 + 1 \cdot 300 + \cdots + 9 \cdot 300 = 45 \cdot 300 = 13500$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12819 :
  ∑ k in (Finset.range 10), (k + 1) * 300 = 13500   :=  by sorry
