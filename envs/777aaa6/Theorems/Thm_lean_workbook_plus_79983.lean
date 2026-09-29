-- Prove2me | Theorems.Thm_lean_workbook_plus_79983
-- name    : lean_workbook_plus_79983
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7c1824f7-b6b1-4fa1-8fee-f4051b38d3c9
-- statement:
--   The $2!$ overcount is actually because there are 2 ways for a person to get the same hand (A, B): he is dealt A, then B, or he is dealt B, then A. Repeating this for 4 people gets you $\frac{8!}{2!^4}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79983 :
  8! / (2!^4) = 90   :=  by sorry
