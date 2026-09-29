-- Prove2me | Theorems.Thm_lean_workbook_plus_39449
-- name    : lean_workbook_plus_39449
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/88ecb6bb-32ef-41f6-83cc-6e47fa6b15c6
-- statement:
--   If such numbers are $x,y$ , then $xy={k(k+1)\over 2}-x-y\iff (x+1)(y+1)={k(k+1)\over 2}+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39449 (x y k : ℤ) : (x * y = k * (k + 1) / 2 - x - y) ↔ (x + 1) * (y + 1) = k * (k + 1) / 2 + 1   :=  by sorry
