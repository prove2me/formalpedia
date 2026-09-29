-- Prove2me | Theorems.Thm_lean_workbook_plus_65893
-- name    : lean_workbook_plus_65893
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d3b2a3f1-7e7f-4fbb-ba15-d9e896efccbc
-- statement:
--   $n\equiv 0\pmod{3}\Rightarrow 3n(n+1)+7\equiv 7\pmod{9}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65893 : ∀ n : ℤ, n % 3 = 0 → (3 * n * (n + 1) + 7) % 9 = 7 % 9   :=  by sorry
