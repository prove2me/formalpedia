-- Prove2me | Theorems.Thm_lean_workbook_plus_44546
-- name    : lean_workbook_plus_44546
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/59679048-88d4-49bb-abfb-4abc615eb3de
-- statement:
--   Prove that if $ab \equiv ac \pmod{ad}$, then $b \equiv c \pmod{d}$ and vice versa.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44546 (a b c d : ℤ) (ha : a ≠ 0) (hd : d ≠ 0) : (a * b ≡ a * c [ZMOD a * d]) ↔ (b ≡ c [ZMOD d])   :=  by sorry
