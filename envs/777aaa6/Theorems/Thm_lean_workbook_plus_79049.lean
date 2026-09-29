-- Prove2me | Theorems.Thm_lean_workbook_plus_79049
-- name    : lean_workbook_plus_79049
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1b7b9a6c-790b-45da-b360-741854a2dd47
-- statement:
--   Prove that ${n + 2 \choose r + 2} = {n \choose r} + 2{n \choose r + 1} + {n \choose r + 2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79049 (n r : ℕ) : choose (n + 2) (r + 2) = choose n r + 2 * choose n (r + 1) + choose n (r + 2)   :=  by sorry
