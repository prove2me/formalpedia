-- Prove2me | Theorems.Thm_lean_workbook_plus_23412
-- name    : lean_workbook_plus_23412
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5db8cb29-47d8-4dba-a704-291f0eb6c9d7
-- statement:
--   Let $n$ be any natural numbers and $x,y$ are real numbers with $0<x<y$ . Is it true that $\sqrt[n]{x}-\sqrt[n]{y}\leq \sqrt[n]{y-x}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23412 (n : ℕ) (x y : ℝ) (hx : x > 0) (hy : y > x) : (x:ℝ) ^ (1 / n) - (y:ℝ) ^ (1 / n) ≤ (y - x:ℝ) ^ (1 / n)   :=  by sorry
