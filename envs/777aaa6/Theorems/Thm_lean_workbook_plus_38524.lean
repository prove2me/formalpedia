-- Prove2me | Theorems.Thm_lean_workbook_plus_38524
-- name    : lean_workbook_plus_38524
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/0842b5e7-5113-4a9d-8b8c-b98771e3fead
-- statement:
--   $ \gcd(n,n+32)=\gcd(n,32)=1$ (since $ n$ is given to be odd)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38524 (n : ℕ) (h : n % 2 = 1) : Nat.gcd n (n + 32) = Nat.gcd n 32   :=  by sorry
