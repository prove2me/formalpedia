-- Prove2me | Theorems.Thm_lean_workbook_plus_21879
-- name    : lean_workbook_plus_21879
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6deb5bf7-77e3-4860-8635-630faa2acbcf
-- statement:
--   Counting these we get $x=\dbinom{6}{4}+\dbinom{5}{4}+11 \left(\dbinom{6}{3}+\dbinom{5}{3} \right)+30\left(\dbinom{6}{2}+\dbinom{5}{2}\right)=1100$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21879 ( choose 6 4 + choose 5 4 + 11*(choose 6 3 + choose 5 3) + 30*(choose 6 2 + choose 5 2) ) = 1100   :=  by sorry
