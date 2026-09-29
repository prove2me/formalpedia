-- Prove2me | Theorems.Thm_lean_workbook_plus_73039
-- name    : lean_workbook_plus_73039
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/16605be9-0549-43c8-b60c-c7d5f901f989
-- statement:
--   Prove that $\text{lcm}(a, b)\text{gcd}(a, b)=ab$ for $a, b\in\mathbb{N}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73039 (a b : ℕ) : Nat.lcm a b * Nat.gcd a b = a * b   :=  by sorry
