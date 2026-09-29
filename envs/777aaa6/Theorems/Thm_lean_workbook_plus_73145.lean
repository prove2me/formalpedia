-- Prove2me | Theorems.Thm_lean_workbook_plus_73145
-- name    : lean_workbook_plus_73145
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/06569741-7b5a-4915-8778-66ccbfe2ac9f
-- statement:
--   After denoting $s=\sum{}\frac{1}{b+1}$ , we just need to prove: $\sqrt{s(3-s)} \le \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73145 (s : ℝ) (hs : s = ∑ b in B, 1 / (b + 1)) :  Real.sqrt (s * (3 - s)) ≤ 3 / 2   :=  by sorry
