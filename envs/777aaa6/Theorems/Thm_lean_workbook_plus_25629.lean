-- Prove2me | Theorems.Thm_lean_workbook_plus_25629
-- name    : lean_workbook_plus_25629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8f2f385e-9f22-4a32-ace2-4ea560c08525
-- statement:
--   Prove $mn = \gcd(m,n)\text{lcm}[m,n]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25629 (m n : ℕ) : m * n = Nat.gcd m n * Nat.lcm m n   :=  by sorry
