-- Prove2me | Theorems.Thm_lean_workbook_plus_55081
-- name    : lean_workbook_plus_55081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/98af8304-2986-4b77-b4e8-ff566f20c59c
-- statement:
--   If $a \equiv b \bmod m$ and $c \equiv d \bmod m$ then $ac \equiv bd \bmod m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55081 (a b c d m : ℤ) (h₁ : a ≡ b [ZMOD m]) (h₂ : c ≡ d [ZMOD m]) : a * c ≡ b * d [ZMOD m]   :=  by sorry
