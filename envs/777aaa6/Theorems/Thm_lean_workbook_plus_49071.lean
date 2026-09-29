-- Prove2me | Theorems.Thm_lean_workbook_plus_49071
-- name    : lean_workbook_plus_49071
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0b7229f8-252d-4522-986a-a8c7fb05a36a
-- statement:
--   (1) First prove by induction that $1+2+3+...+m=\frac {m(m+1)} 2$ (which is too easy or straight forward) and then set $m=2^{n-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49071 : ∀ n : ℕ, ∑ i in Finset.range (2^(n-1)), i = 2^(n-1) * (2^(n-1) + 1) / 2   :=  by sorry
