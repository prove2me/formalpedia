-- Prove2me | Theorems.Thm_lean_workbook_plus_31866
-- name    : lean_workbook_plus_31866
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e6a318dd-b6b4-4abe-9440-92124542c8fe
-- statement:
--   Let $ a_n = \left(\frac {n}{n + 1}\right)^{n^2} = \left(1 - \frac1{n + 1}\right)^{n^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31866 (n : ℕ) : ((n:ℝ) / (n + 1))^(n^2) = (1 - (1 / (n + 1)))^(n^2)   :=  by sorry
