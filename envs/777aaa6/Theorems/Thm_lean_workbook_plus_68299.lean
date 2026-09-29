-- Prove2me | Theorems.Thm_lean_workbook_plus_68299
-- name    : lean_workbook_plus_68299
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/84bc53f6-bb4c-44de-afb4-e5c75874f807
-- statement:
--   prove $\dfrac{1}{2}+\dfrac{1}{4}+\dfrac{1}{8}+...+\dfrac{1}{2^n}<1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68299 : ∀ n, ∑ i in Finset.range n, (1 / (2 ^ i)) < 1   :=  by sorry
