-- Prove2me | Theorems.Thm_lean_workbook_plus_21
-- name    : lean_workbook_plus_21
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/48684d42-4135-49c4-8987-84f7896945e9
-- statement:
--   Prove that $\binom{n-q}{p-q}\binom{n}{q}=\binom{n}{p}\binom{p}{q}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21 (n p q : ℕ) (hp : p ≤ n) (hq : q ≤ p) : (n - q).choose (p - q) * n.choose q = n.choose p * p.choose q   :=  by sorry
