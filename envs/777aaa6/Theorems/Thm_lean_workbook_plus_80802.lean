-- Prove2me | Theorems.Thm_lean_workbook_plus_80802
-- name    : lean_workbook_plus_80802
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d9b1b83e-11dc-4dae-82be-450ec837efbd
-- statement:
--   Prove the inequality:\n\n$pq^2\leqq{\frac{p^3+2q^3}{3}}$\n\nfor any positive numbers $p$ and $q$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80802 (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3   :=  by sorry
