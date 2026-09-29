-- Prove2me | Theorems.Thm_lean_workbook_plus_7991
-- name    : lean_workbook_plus_7991
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3df42fc2-3f81-498b-b63d-e5492e6c34b2
-- statement:
--   Prove that if $ \gcd(a,b)=1$ then $ \gcd(ab,a+b)=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7991 (a b : ℕ) : Nat.Coprime a b → Nat.Coprime (a * b) (a + b)   :=  by sorry
