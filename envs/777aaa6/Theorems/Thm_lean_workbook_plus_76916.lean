-- Prove2me | Theorems.Thm_lean_workbook_plus_76916
-- name    : lean_workbook_plus_76916
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/d7de5ed7-e7f0-48fb-a8be-0bc3f78f4609
-- statement:
--   We see that: $60=(2-1) \cdot 60$, $60=(3-1) \cdot 30$, $60 = (5-1) \cdot 15$, $60 = (7-1) \cdot 10$, $60 = (11-1) \cdot 6$, $60 = (13-1) \cdot 5$, $60 = (31-1) \cdot 2$, $60 = (61-1) \cdot 60$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76916 : {n : ℕ | 1 < n ∧ (n-1)∣60} = {2,3,5,7,11,13,31,61}   :=  by sorry
