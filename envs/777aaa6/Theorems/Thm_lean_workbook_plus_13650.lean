-- Prove2me | Theorems.Thm_lean_workbook_plus_13650
-- name    : lean_workbook_plus_13650
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c4299682-8368-4441-bc99-58f178b53877
-- statement:
--   Explain the solution: \n$\binom{16}{2}\binom{14}{2}\cdots\binom{2}{2} = \frac{16 \cdot 15 \cdots 2}{2 \cdot 2 \cdots 2} = \frac{16!}{2^8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13650 :
  ∏ k in Finset.Icc 1 8, (16 - 2 * k).choose 2 = (16! / 2^8)   :=  by sorry
