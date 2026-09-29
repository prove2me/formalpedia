-- Prove2me | Theorems.Thm_lean_workbook_plus_66490
-- name    : lean_workbook_plus_66490
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f071f94d-7bb9-4b5a-ba7c-a35dfce4a47b
-- statement:
--   We use balls and urns for each distribution of green flags: $0$ on left pole, $9$ on right: $\binom{1}{0}*\binom{11}{9}+\binom{2}{0}*\binom{10}{9}+\binom{3}{0}*\binom{9}{9}+....+\binom{11}{0}*\binom{1}{9}$ $1$ on left pole, $8$ on right: $\binom{1}{1}*\binom{11}{8}+\binom{2}{1}*\binom{10}{8}+\binom{3}{1}*\binom{9}{8}+....+\binom{11}{1}*\binom{1}{8}$ ... $9$ on left pole, $0$ on right: $\binom{1}{9}*\binom{11}{0}+\binom{2}{9}*\binom{10}{0}+\binom{3}{9}*\binom{9}{0}+....+\binom{11}{9}*\binom{1}{0}$ Using combinatorial identities, we can simplify this to $11*\binom{12}{9}=2420\equiv 420 (mod 1000).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66490 :
  (∑ k in Finset.Icc 0 9, (k + 1) * (Nat.choose 12 9 - Nat.choose k 9)) % 1000 = 420   :=  by sorry
