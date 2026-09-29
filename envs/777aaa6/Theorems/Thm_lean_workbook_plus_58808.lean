-- Prove2me | Theorems.Thm_lean_workbook_plus_58808
-- name    : lean_workbook_plus_58808
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d9e5106a-be99-4063-aaf4-1bbece753743
-- statement:
--   $x\equiv r\mod q,y\equiv s\mod q$ ,then we have $xy\equiv rs\mod q$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58808 (x r y s : ℤ) (q : ℕ) (h₁ : x ≡ r [ZMOD q]) (h₂ : y ≡ s [ZMOD q]) :
  x * y ≡ r * s [ZMOD q]   :=  by sorry
