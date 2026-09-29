-- Prove2me | Theorems.Thm_lean_workbook_plus_12366
-- name    : lean_workbook_plus_12366
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/2600c4ec-d367-42da-a96c-9416eedef860
-- statement:
--   $(1+x)^{2020}=\binom{2020}{0}+x\binom{2020}{1}+ \cdots + x^{2020}\binom{2020}{2020}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12366 (x : ℝ) : (1+x)^2020 = ∑ i in Finset.range 2021, x^i * (Nat.choose 2020 i)   :=  by sorry
