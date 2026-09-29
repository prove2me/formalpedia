-- Prove2me | Theorems.Thm_lean_workbook_plus_39730
-- name    : lean_workbook_plus_39730
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/baa2bdf0-4a9a-458d-892f-dc7a03a95f9b
-- statement:
--   even numbers: $2, 4, 6, 8, 10$ \nodd numbers: $1, 3, 5, 7, 9, 11$ \nTo get an odd sum we must have: $ \{ \begin{array}{lll} 1 \textrm{\,odd and\,} 5 \textrm{\,even} \ 3 \textrm{\,odd and\,} 3 \textrm{\,even} \ 5 \textrm{\,odd and\,} 1 \textrm{\,even} \end{array}$ \nTherefore our probability is $\frac{ \displaystyle{ {6 \choose 1} \cdot {5 \choose 5} + {6 \choose 3} \cdot {5\choose 3} + {6\choose 5} \cdot {5\choose 1}}} {\displaystyle {{11 \choose 6}}}=\frac{118}{231}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39730 :
  ((6).choose 1 * (5).choose 5 + (6).choose 3 * (5).choose 3 + (6).choose 5 * (5).choose 1) / (11).choose 6 = 118 / 231   :=  by sorry
