-- Prove2me | Theorems.Thm_lean_workbook_plus_23725
-- name    : lean_workbook_plus_23725
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e683477b-0c0f-4a62-96cb-387b8d93c7c6
-- statement:
--   Proove that, for any $ n$ non-negative integer, the number $ 1^n + 2^n + 3^n + 4^n$ is divisible by 5 if, and only if, $ n$ is not divisible by 4.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23725 (n:ℕ) : n % 4 ≠ 0 ↔ (1^n + 2^n + 3^n + 4^n) % 5 = 0   :=  by sorry
