-- Prove2me | Theorems.Thm_lean_workbook_plus_56500
-- name    : lean_workbook_plus_56500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/a7e1285c-9b7c-4ffb-85ff-29ee335036ef
-- statement:
--   The number of ways of getting exactly 2 heads from tossing 4 coins is $\binom{4} {2}=6$ . There are $2^4=16$ total possibilities, so the probability is $\frac{6}{16}=\boxed{\frac{3}{8}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56500 :
  ((Nat.choose 4 2) : ℚ) / (2^4) = 3 / 8   :=  by sorry
