-- Prove2me | Theorems.Thm_lean_workbook_plus_60758
-- name    : lean_workbook_plus_60758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c9715e1e-3702-4322-a53a-d71c06f3da00
-- statement:
--   Prove that $ n + x = k^2$ and $ n + y = (k + 1)^2$ with $ n,x,y \in \mathbb Z$ implies $ x = k^2 - n$ and $ y = (k + 1)^2 - n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60758 (n x y k : ℤ) : n + x = k^2 ∧ n + y = (k + 1)^2 → x = k^2 - n ∧ y = (k + 1)^2 - n   :=  by sorry
