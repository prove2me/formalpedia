-- Prove2me | Theorems.Thm_lean_workbook_plus_48865
-- name    : lean_workbook_plus_48865
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/72b58b94-4337-4a4b-9bba-2f6df9665dca
-- statement:
--   A binary function $*$ is said to be 'commutative' if it satisfies: $x*y=y*x$ for all $x$ and $y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48865 (f : ℕ → ℕ → ℕ) : (∀ x y : ℕ, f x y = f y x) ↔ Commutative f   :=  by sorry
