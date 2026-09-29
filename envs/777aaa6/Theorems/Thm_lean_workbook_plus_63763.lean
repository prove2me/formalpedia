-- Prove2me | Theorems.Thm_lean_workbook_plus_63763
-- name    : lean_workbook_plus_63763
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/3e3d1b04-878a-493e-929f-14872da2334b
-- statement:
--   Prove that $ A\cap (B-C)\subseteq (A\cap B)-(A\cap C) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63763 (A B C : Set α) : A ∩ (B \ C) ⊆ (A ∩ B) \ (A ∩ C)   :=  by sorry
