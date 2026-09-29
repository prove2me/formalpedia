-- Prove2me | Theorems.Thm_lean_workbook_plus_77091
-- name    : lean_workbook_plus_77091
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/3ba419a3-0371-4979-b988-7d4469ca9af4
-- statement:
--   Prove that if $a \equiv c \pmod{k}$ and $b \equiv d \pmod{k}$, then $a+b \equiv c+d \pmod{k}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77091 (a b c d k : ℤ) (h₁ : a ≡ c [ZMOD k]) (h₂ : b ≡ d [ZMOD k]) : a + b ≡ c + d [ZMOD k]   :=  by sorry
