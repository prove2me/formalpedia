-- Prove2me | Theorems.Thm_lean_workbook_plus_19864
-- name    : lean_workbook_plus_19864
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1e909f58-f4b0-4437-acbc-3185bcf5061c
-- statement:
--   Prove the distributive law of set theory: $ A\cup (B\cap C) $ = $ (A\cup B)\cap (A\cup C) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19864 (A B C : Set α) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)   :=  by sorry
