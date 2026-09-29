-- Prove2me | Theorems.Thm_lean_workbook_plus_37275
-- name    : lean_workbook_plus_37275
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/7885df6a-2d0f-4f80-a6b6-a113529137b0
-- statement:
--   As a quick tutorial on mods, since it is an important topic, $a \equiv b \pmod m$ just means that $a$ and $b$ have the same remainder when divided by $m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37275  (a b m : ℤ)
  (h₀ : 0 < m)
  (h₁ : a ≡ b [ZMOD m]) :
  a % m = b % m   :=  by sorry
