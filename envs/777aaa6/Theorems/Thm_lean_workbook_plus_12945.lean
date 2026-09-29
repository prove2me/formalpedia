-- Prove2me | Theorems.Thm_lean_workbook_plus_12945
-- name    : lean_workbook_plus_12945
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c8f5d994-d362-48db-af33-1119a78cbd51
-- statement:
--   Prove that $\phi(mn)=\phi(m).\phi(n)$ if gcd(m,n)= $1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12945 (m n : ℕ) : Coprime m n → φ (m * n) = φ m * φ n   :=  by sorry
