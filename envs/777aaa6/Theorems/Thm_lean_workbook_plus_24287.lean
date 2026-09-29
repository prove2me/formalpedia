-- Prove2me | Theorems.Thm_lean_workbook_plus_24287
-- name    : lean_workbook_plus_24287
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/12b249e3-adb0-4e5c-9c30-b2598615b7cd
-- statement:
--   Prove that if $a$ and $b$ are coprime, and $a$ is a divisor of $bc$, then $a$ must be divisible by $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24287 (a b c : ℕ) (hab : Nat.Coprime a b) (hbc : b * c ≠ 0) (h : a ∣ b * c) : a ∣ c   :=  by sorry
