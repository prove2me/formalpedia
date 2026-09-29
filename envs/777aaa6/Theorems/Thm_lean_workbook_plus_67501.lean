-- Prove2me | Theorems.Thm_lean_workbook_plus_67501
-- name    : lean_workbook_plus_67501
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/87fca80e-9cdb-4418-8196-25e153d1d29c
-- statement:
--   $(3 + 3)^3 = 3^3\cdot 3^0 + 3(3^2 \cdot 3^1) + 3(3^1 \cdot 3^2) + 3^0\cdot 3^3$ by the binomial theorem. You only need the first three terms - the last term is the all nonprime way.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67501 (3 + 3) ^ 3 = 3 ^ 3 * 3 ^ 0 + 3 * (3 ^ 2 * 3 ^ 1) + 3 * (3 ^ 1 * 3 ^ 2) + 3 ^ 0 * 3 ^ 3   :=  by sorry
