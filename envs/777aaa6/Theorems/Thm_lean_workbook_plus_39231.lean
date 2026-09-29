-- Prove2me | Theorems.Thm_lean_workbook_plus_39231
-- name    : lean_workbook_plus_39231
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/f770f8d6-6c23-41d4-98a9-58fd0051d517
-- statement:
--   ${3 \choose 1} {2 \choose 1} {1 \choose 1} = 6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39231 (h : 3 > 0 ∧ 2 > 0 ∧ 1 > 0) : (Nat.choose 3 1 * Nat.choose 2 1 * Nat.choose 1 1) = 6   :=  by sorry
