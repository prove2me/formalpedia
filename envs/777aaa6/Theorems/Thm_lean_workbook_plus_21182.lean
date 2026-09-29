-- Prove2me | Theorems.Thm_lean_workbook_plus_21182
-- name    : lean_workbook_plus_21182
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/57b3fbf2-d29c-49fa-ae54-43a7dc17aff1
-- statement:
--   (b) In general, $ (n - 1)! \cdot 2^{n - 1}\cdot \prod_{k = 1}^{n}{(2k - 1)} = (2n - 1)!$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21182 : ∀ n : ℕ, (n - 1)! * 2 ^ (n - 1) * ∏ k in Finset.range n, (2 * k - 1) = (2 * n - 1)!   :=  by sorry
