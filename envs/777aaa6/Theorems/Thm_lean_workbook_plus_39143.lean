-- Prove2me | Theorems.Thm_lean_workbook_plus_39143
-- name    : lean_workbook_plus_39143
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/470c57ca-ccd3-4676-b20a-75f824cd5ff2
-- statement:
--   $\frac{n^{2}-71}{7n+55} \in \mathbb Z \implies 7n+55 | n^2 -71$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39143 (n : ℤ) : (n^2 - 71) % (7 * n + 55) = 0 ↔ 7 * n + 55 ∣ n^2 - 71   :=  by sorry
