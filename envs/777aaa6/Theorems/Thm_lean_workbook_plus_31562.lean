-- Prove2me | Theorems.Thm_lean_workbook_plus_31562
-- name    : lean_workbook_plus_31562
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/4ae0dbf0-de92-443f-980b-c011d4a4c25e
-- statement:
--   Prove by induction that $1^2 + 2^2 + 3^2 + \ldots + n^2 = \frac{n(n+1)(2n+1)}{6}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31562 : ∀ n, ∑ i in Finset.range n, i^2 = n * (n + 1) * (2 * n + 1) / 6   :=  by sorry
