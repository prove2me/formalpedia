-- Prove2me | Theorems.Thm_lean_workbook_plus_58227
-- name    : lean_workbook_plus_58227
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2b95dee0-0b93-48d0-b813-e2f3071bd06b
-- statement:
--   An even square is congruent to $0 \pmod{4},$ while an odd square is congruent to $1 \pmod{4}.$ This can be proven $(2k)^2=4k^2=0 \pmod{4}$ ; $(2k+1)^2=4k^2+4k+1=1 \pmod{4}$ by representing even numbers as $2k$ and odd numbers as $2k+1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58227 : ∀ n : ℤ, Even n → n^2 % 4 = 0   :=  by sorry
