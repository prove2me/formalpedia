-- Prove2me | Theorems.Thm_lean_workbook_plus_34475
-- name    : lean_workbook_plus_34475
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/3808d77f-821d-473e-9abb-85ef363f24bb
-- statement:
--   $10^5 \equiv 10^4 \cdot 10 \equiv 1 \cdot 10 \equiv 10 \pmod {101}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34475 :
  (10^5) % 101 = (10^4 * 10) % 101   :=  by sorry
