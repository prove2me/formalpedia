-- Prove2me | Theorems.Thm_lean_workbook_plus_35427
-- name    : lean_workbook_plus_35427
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1f625eec-8234-47ef-af5e-e990a0cd4ba0
-- statement:
--   Prove that if $e^{z}f(z) = k [f(z)+e^{z}]$ and $k \neq 0$, then $f(z) = 0$ for all $z \in C$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35427 (f : ℂ → ℂ) (k : ℂ) (h : k ≠ 0) (hf : ∀ z, exp z * f z = k * (f z + exp z)) : ∀ z, f z = 0   :=  by sorry
