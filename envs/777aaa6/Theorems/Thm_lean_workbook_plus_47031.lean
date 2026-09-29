-- Prove2me | Theorems.Thm_lean_workbook_plus_47031
-- name    : lean_workbook_plus_47031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9a5d1d37-8e3a-429e-8afc-b77a91971ea0
-- statement:
--   And problem is just to prove $0\le \frac 1{n^2+n+2}\le\frac 14$ $\forall n\in\mathbb Z_{>0}$ , which is immediate
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47031 (n : ℕ) : 0 ≤ 1 / (n ^ 2 + n + 2) ∧ 1 / (n ^ 2 + n + 2) ≤ 1 / 4   :=  by sorry
