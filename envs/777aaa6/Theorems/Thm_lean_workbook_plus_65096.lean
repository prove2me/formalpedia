-- Prove2me | Theorems.Thm_lean_workbook_plus_65096
-- name    : lean_workbook_plus_65096
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/41bd1b4b-147b-4aad-b3cb-1d3fd6c4a077
-- statement:
--   To evaluate this, consider \(\sum_{k=3}^{51}\frac {\binom{k}{3}\cdot \binom{52 - k}{1} }{\binom{52}{4}}\cdot k=\frac{3}{\binom{52}{4} }\sum_{k=3}^{51} \binom{k}{3}\cdot \binom{52 - k}{1}\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65096 ∑ k in (Finset.Icc 3 51), (k * (Nat.choose k 3 * Nat.choose (52 - k) 1)) / (Nat.choose 52 4) = 3 * ∑ k in (Finset.Icc 3 51), (Nat.choose k 3 * Nat.choose (52 - k) 1) / (Nat.choose 52 4)   :=  by sorry
