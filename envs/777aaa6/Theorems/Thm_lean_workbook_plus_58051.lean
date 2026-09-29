-- Prove2me | Theorems.Thm_lean_workbook_plus_58051
-- name    : lean_workbook_plus_58051
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f885cac0-59ac-42a6-8120-bf392c247311
-- statement:
--   A function $f$ is surjective if for every value $b$ in the co-domain of a function, there exists at least one value $a$ such that $f(a)=b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58051 {f : ℕ → ℕ} : (∀ b, ∃ a, f a = b) ↔ Function.Surjective f   :=  by sorry
