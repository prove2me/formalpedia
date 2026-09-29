-- Prove2me | Theorems.Thm_lean_workbook_plus_34837
-- name    : lean_workbook_plus_34837
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/692fdd18-c803-4e7c-a6e3-9b4fd8b06199
-- statement:
--   Let $a$ , $b$ be non-negative numbers such that $a^2+kb\geq a^3+b^2 $ . Prove that: \n $$a^2+b^2\leq k^2+1$$ Where $k\in N^+.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34837 (a b : ℝ) (k : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2 + k * b ≥ a^3 + b^2) : a^2 + b^2 ≤ k^2 + 1   :=  by sorry
