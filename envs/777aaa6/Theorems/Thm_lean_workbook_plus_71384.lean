-- Prove2me | Theorems.Thm_lean_workbook_plus_71384
-- name    : lean_workbook_plus_71384
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7a178808-a5c0-4c1f-bc53-f47fc611eb54
-- statement:
--   Prove the Euclidean Algorithm: For integers $a > b$, show that $gcd(a, b) = gcd(a - b, b)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71384 (a b : ℤ) (h : a > b) : gcd a b = gcd (a - b) b   :=  by sorry
