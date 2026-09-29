-- Prove2me | Theorems.Thm_lean_workbook_plus_38066
-- name    : lean_workbook_plus_38066
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a9376e60-e1d2-4d12-9313-459bcb210f44
-- statement:
--   Prove that $\binom{p-1}{(p-1)/2}\equiv (-1)^\frac{p-1}{2}\pmod{p}$ for odd prime $p$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38066 (p : ℕ) (hp : p.Prime) (hpo : Odd p) :
    ((p - 1).choose (p - 1) / 2) ≡ (-1 : ℤ) ^ (p - 1) / 2 [ZMOD p]   :=  by sorry
