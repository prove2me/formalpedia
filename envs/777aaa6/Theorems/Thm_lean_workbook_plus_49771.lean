-- Prove2me | Theorems.Thm_lean_workbook_plus_49771
-- name    : lean_workbook_plus_49771
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/7c709cbb-5fcf-49fe-b6f6-8a68e9b4b68c
-- statement:
--   Prove that $\sum_{m=0}^{15}\sum_{n=0}^{15-m}\binom{m+n}{m}\binom{15}{m+n}5^n = \sum_{m=0}^{15}\binom{15}{m}6^{15-m}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49771 : ∑ m in Finset.range 16, ∑ n in Finset.range (16 - m), (Nat.choose (m + n) m * Nat.choose 15 (m + n) * 5 ^ n) = ∑ m in Finset.range 16, (Nat.choose 15 m * 6 ^ (15 - m))   :=  by sorry
