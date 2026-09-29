-- Prove2me | Theorems.Thm_lean_workbook_plus_81245
-- name    : lean_workbook_plus_81245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a038ba3a-705f-4725-9de1-909cef638312
-- statement:
--   Prove that $t^m+\frac 1{t^m}\in\mathbb N$ if $t+\frac 1t\in\mathbb N$, where $t\ge 1$ and $m\in\mathbf{N}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81245 (t : ℕ) (m : ℕ) (ht : 1 ≤ t) (h : t + 1/t ∈ Set.range (Nat.cast)) : t^m + 1/(t^m) ∈ Set.range (Nat.cast)   :=  by sorry
