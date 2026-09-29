-- Prove2me | Theorems.Thm_lean_workbook_plus_73394
-- name    : lean_workbook_plus_73394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/552bc23c-101b-45e6-8d18-10056c912015
-- statement:
--   You get 2 prompts: \n $\frac{\binom{2}{2}\cdot\binom{4}{1}}{\binom{6}{3}}=\frac{1}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73394 :
  ((Nat.choose 2 2 * Nat.choose 4 1) / Nat.choose 6 3) = 1 / 5   :=  by sorry
