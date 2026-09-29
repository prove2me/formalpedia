-- Prove2me | Theorems.Thm_lean_workbook_plus_45014
-- name    : lean_workbook_plus_45014
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b8982d75-85eb-481d-932c-6e24a7828826
-- statement:
--   Given $a \equiv 1$ or $2 \pmod 3$, prove that $a^2 \equiv 1 \pmod 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45014 (a : ℤ) (h : a ≡ 1 [ZMOD 3] ∨ a ≡ 2 [ZMOD 3]) : a^2 ≡ 1 [ZMOD 3]   :=  by sorry
