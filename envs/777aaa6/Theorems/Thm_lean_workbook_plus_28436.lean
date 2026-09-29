-- Prove2me | Theorems.Thm_lean_workbook_plus_28436
-- name    : lean_workbook_plus_28436
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/42676004-ca9c-488d-a6f3-2301de6a20a6
-- statement:
--   Case 1: The $1$ and $7$ do not leave 3rd 4th or 5th. This happens with probability $\frac{\binom{4}{2}}{21} = \frac{6}{21}$ . Then the probability that the 3rd 4th and 5th people leave in age order is $\frac{\binom{5}{3} \cdot 2!}{5!} = \frac{1}{6}$ since there are $\binom{5}{3}$ ways to choose the 3rd 4th and 5th person and $2!$ ways to order the rest.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28436 (Nat.choose 4 2)/21 * (Nat.choose 5 3 * 2!)/5! = 1/6   :=  by sorry
