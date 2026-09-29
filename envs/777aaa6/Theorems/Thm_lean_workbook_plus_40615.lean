-- Prove2me | Theorems.Thm_lean_workbook_plus_40615
-- name    : lean_workbook_plus_40615
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/88e0b22f-1b18-4070-bd4e-0313523eea3e
-- statement:
--   Prove that $ \prod_{k=2}^{n} {\frac {(k-1)(k^2+k)}{k^3}} = \prod_{k=2}^{n} {\frac {k^2-1}{k^2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40615 : ∀ n, (∏ k in (Finset.range (n + 1)).filter (· ≠ 1), (k - 1) * (k ^ 2 + k) / k ^ 3) = (∏ k in (Finset.range (n + 1)).filter (· ≠ 1), (k ^ 2 - 1) / k ^ 2)   :=  by sorry
