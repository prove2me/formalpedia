-- Prove2me | Theorems.Thm_lean_workbook_plus_18858
-- name    : lean_workbook_plus_18858
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/aacc33ef-e78e-430e-a027-ae2359f127af
-- statement:
--   And $\phi (mn)= \phi (m) \phi (n)$ only when $gcd(m;n)=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18858 (m n : ℕ) (h : Nat.Coprime m n) : φ m * φ n = φ (m * n)   :=  by sorry
