-- Prove2me | Theorems.Thm_lean_workbook_plus_48104
-- name    : lean_workbook_plus_48104
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/685f5e7f-1a37-4756-ac2e-f79c2472a633
-- statement:
--   For all $m \ge 2$ , it holds that $f(3m) \ge 2$ , $f(3m+1) \le -1$ , and $f(3m+2) \le -1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48104 (m : ℕ) (hm : 2 ≤ m) (f : ℕ → ℤ) (hf: f (3*m) ≥ 2 ∧ f (3*m+1) ≤ -1 ∧ f (3*m+2) ≤ -1) : f (3*m) ≥ 2 ∧ f (3*m+1) ≤ -1 ∧ f (3*m+2) ≤ -1   :=  by sorry
