-- Prove2me | Theorems.Thm_lean_workbook_plus_81291
-- name    : lean_workbook_plus_81291
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b27cde0a-3f85-4626-b2bd-7f13ff56f74e
-- statement:
--   Say $P(x)=\frac {1} {2} x$ and $Q(x) = x+1$ ; then $P(2) = Q(2k)$ leads to $2k = 0$ , so $k=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81291 (k : ℤ) (P Q : ℤ → ℤ) (hP : P = fun x => x / 2) (hQ : Q = fun x => x + 1) (h : P 2 = Q (2 * k)) : k = 0   :=  by sorry
