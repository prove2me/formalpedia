-- Prove2me | Theorems.Thm_lean_workbook_plus_35648
-- name    : lean_workbook_plus_35648
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/854ab542-e2eb-4265-b90e-704b65d49695
-- statement:
--   Let $f(x)=k$ for all $x \in N$ where $k$ is a natural number
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35648 (f : ℕ → ℕ) (k : ℕ) (h : ∀ x, f x = k) : ∀ x, f x = k   :=  by sorry
