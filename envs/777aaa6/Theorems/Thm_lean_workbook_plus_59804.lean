-- Prove2me | Theorems.Thm_lean_workbook_plus_59804
-- name    : lean_workbook_plus_59804
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5307eb71-fda4-46b8-9831-c9a4f15a6a03
-- statement:
--   Prove that $ f(n)=1$ if and only if $ n=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59804 (f : ℕ → ℕ) (hf: f n = 1 ↔ n = 1) : f n = 1 ↔ n = 1   :=  by sorry
