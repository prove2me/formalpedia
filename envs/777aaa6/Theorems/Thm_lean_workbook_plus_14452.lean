-- Prove2me | Theorems.Thm_lean_workbook_plus_14452
-- name    : lean_workbook_plus_14452
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/11a798b7-a6c7-465a-a7ae-8c4b0a45b4f0
-- statement:
--   Let $s(n)$ have $n$ ones. $\ n\equiv 1\pmod{3}\,\Rightarrow\, 3\mid s(n)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14452 (n : ℕ) (hn : n ≡ 1 [ZMOD 3]) : 3 ∣ (∑ k in Finset.range n, 1)   :=  by sorry
