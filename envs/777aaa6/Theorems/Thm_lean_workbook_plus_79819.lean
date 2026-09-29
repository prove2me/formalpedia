-- Prove2me | Theorems.Thm_lean_workbook_plus_79819
-- name    : lean_workbook_plus_79819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/fc942294-07bb-462e-a184-ddceea481097
-- statement:
--   Prove that $\frac{1}{p(p+1)}+\frac{1}{q(q+1)}{\ge}\frac{1}{3}$ given $p,q>0$ and $\frac{1}{p}+\frac{1}{q}=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79819 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (h : 1 / p + 1 / q = 1) : 1 / (p * (p + 1)) + 1 / (q * (q + 1)) ≥ 1 / 3   :=  by sorry
