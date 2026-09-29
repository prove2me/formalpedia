-- Prove2me | Theorems.Thm_lean_workbook_plus_36616
-- name    : lean_workbook_plus_36616
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/3ae903fb-14b0-4b9f-acc1-977d8ce84432
-- statement:
--   At each basketball practice last week, Jenny made twice as many free throws as she made at the previous practice. At her fifth practice she made $ 48$ free throws. How many free throws did she make at the first practice?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36616 (x : ℝ) (hx : 2 * (2 * (2 * (2 * x))) = 48) : x = 3   :=  by sorry
