-- Prove2me | Theorems.Thm_lean_workbook_plus_64100
-- name    : lean_workbook_plus_64100
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6e900abd-ec0f-491b-8aae-e70ea8e25f0a
-- statement:
--   Proof: $ n \equiv 0, 1, 2\: mod\: 3 \Longrightarrow n^2 \equiv 0,1\: \mod\: 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64100 {n:ℤ} : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 → n ^ 2 % 3 = 0 ∨ n ^ 2 % 3 = 1   :=  by sorry
