-- Prove2me | Theorems.Thm_lean_workbook_plus_47605
-- name    : lean_workbook_plus_47605
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/dabb7a02-0a52-4ac5-ba60-672cae89aaf7
-- statement:
--   What is $(2 + 4 + ... + 20) - (1 + 3 + ...+ 19)$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47605 : (∑ k in Finset.Icc 1 10, (2 * k)) - (∑ k in Finset.Icc 1 10, (2 * k - 1)) = 10   :=  by sorry
