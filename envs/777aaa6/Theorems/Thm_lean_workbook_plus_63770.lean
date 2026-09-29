-- Prove2me | Theorems.Thm_lean_workbook_plus_63770
-- name    : lean_workbook_plus_63770
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f418eeb8-3817-49b6-b75f-3eddb799a3bf
-- statement:
--   Prove that if $n=p^t$ , then $v_{p}(C_{n}^{p^{t-1}})=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63770 (p t : ℕ) (hp : p.Prime) (ht : t ≠ 0)
    : multiplicity p (choose (p^t) (p^(t-1))) = 1   :=  by sorry
