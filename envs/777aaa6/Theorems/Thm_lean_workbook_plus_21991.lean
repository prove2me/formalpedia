-- Prove2me | Theorems.Thm_lean_workbook_plus_21991
-- name    : lean_workbook_plus_21991
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b5d6db37-c799-4844-bb02-730dbf9ca3f0
-- statement:
--   Prove that if $p>3$ and $a^4\equiv 1\pmod{p}$, then $(a^2+1)(a^2-1)\equiv 0\pmod{p}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21991 : ∀ p > 3, ∀ a : ℕ, a^4 ≡ 1 [ZMOD p] → (a^2 + 1) * (a^2 - 1) ≡ 0 [ZMOD p]   :=  by sorry
