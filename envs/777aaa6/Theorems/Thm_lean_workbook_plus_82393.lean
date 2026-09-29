-- Prove2me | Theorems.Thm_lean_workbook_plus_82393
-- name    : lean_workbook_plus_82393
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/919a53ee-ebb9-4e87-ab4b-3db6eb2ae9d0
-- statement:
--   Prove that $n^2 = 1 + 3 + 5 + ... + 2n - 3 + 2n - 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82393 : ∀ n, n^2 = (∑ i in Finset.range n, (2 * i - 1))   :=  by sorry
