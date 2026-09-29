-- Prove2me | Theorems.Thm_lean_workbook_plus_61497
-- name    : lean_workbook_plus_61497
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/77eed2ab-4835-40cc-b623-d6168a69839c
-- statement:
--   If $ p$ is prime and $ p|bc,$ then prove that $ p|b$ or $ p|c.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61497 (p : ℕ) (b c : ℕ) (hp : p.Prime) (h : p ∣ b * c) : p ∣ b ∨ p ∣ c   :=  by sorry
