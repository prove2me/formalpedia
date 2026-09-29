-- Prove2me | Theorems.Thm_lean_workbook_plus_49848
-- name    : lean_workbook_plus_49848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/850f8abf-b847-4663-92e2-906846d623f1
-- statement:
--   Let $f$ be a function such that $|f(x)|\leq x^2$ for all $x$ . Prove that $f(0)=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49848 (f : ℝ → ℝ) (hf : ∀ x, ‖f x‖ ≤ x^2) : f 0 = 0   :=  by sorry
