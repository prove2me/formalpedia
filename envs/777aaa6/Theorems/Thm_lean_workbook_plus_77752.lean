-- Prove2me | Theorems.Thm_lean_workbook_plus_77752
-- name    : lean_workbook_plus_77752
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/6149b2a1-b7e3-4615-b0a7-9d33ef012816
-- statement:
--   $\left\lfloor\sqrt[k]n\right\rfloor=m$ $\iff$ $m+1>n^{\frac 1k}\ge m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77752 (n m : ℕ) (k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⌊(n:ℝ)^(1/k)⌋ = m) ↔ (m + 1 > (n:ℝ)^(1/k) ∧ (n:ℝ)^(1/k) ≥ m)   :=  by sorry
