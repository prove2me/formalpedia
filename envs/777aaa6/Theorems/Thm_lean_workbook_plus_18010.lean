-- Prove2me | Theorems.Thm_lean_workbook_plus_18010
-- name    : lean_workbook_plus_18010
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/97be5971-09e9-4599-8ac1-bb84410d957d
-- statement:
--   Prove $(a-b)(b-c)(\sum_{i=0}^{x-1}a^{x-1-i}b^i-\sum_{i=0}^{x-1}b^{x-1-i}c^i)\geq 0$ where $a \ge b \ge c \ge 0$ and $x \ge 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18010 (a b c x : ℕ) (ha : a ≥ b) (hb : b ≥ c) (hc : c ≥ 0) (hx : x ≥ 1) : (a - b) * (b - c) * (∑ i in Finset.range x, a ^ (x - 1 - i) * b ^ i - ∑ i in Finset.range x, b ^ (x - 1 - i) * c ^ i) ≥ 0   :=  by sorry
