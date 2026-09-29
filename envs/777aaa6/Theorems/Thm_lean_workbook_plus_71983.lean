-- Prove2me | Theorems.Thm_lean_workbook_plus_71983
-- name    : lean_workbook_plus_71983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2698b18b-7043-4dc8-b462-fe2c177993ed
-- statement:
--   Rewrite as $4q<-4p-1$ , so $q<-p-1/4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71983 (p q : ℝ) : 4 * q < 4 * p - 1 ↔ q < p - 1 / 4   :=  by sorry
