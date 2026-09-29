-- Prove2me | Theorems.Thm_lean_workbook_plus_5838
-- name    : lean_workbook_plus_5838
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a954a30c-4abf-4d5b-b957-e848153a205f
-- statement:
--   Prove that if $a \equiv b \pmod m$, then $a^n \equiv b^n \pmod m$ for any positive integer $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5838 (a b m : ℤ) (n : ℕ) (h₁ : a ≡ b [ZMOD m]) : a ^ n ≡ b ^ n [ZMOD m]   :=  by sorry
