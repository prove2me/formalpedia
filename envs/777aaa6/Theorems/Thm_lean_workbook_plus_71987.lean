-- Prove2me | Theorems.Thm_lean_workbook_plus_71987
-- name    : lean_workbook_plus_71987
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/eabec07c-4ff3-4235-9de3-2fcfeb68f362
-- statement:
--   Given $a_{1}\equiv a_{2}\pmod{8}$, prove that $a_{1}+k \equiv a_{2}+k \pmod{8}$ for any integer $k$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71987 (a₁ a₂ k : ℤ) (h : a₁ ≡ a₂ [ZMOD 8]) : a₁ + k ≡ a₂ + k [ZMOD 8]   :=  by sorry
