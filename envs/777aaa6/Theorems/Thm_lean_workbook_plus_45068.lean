-- Prove2me | Theorems.Thm_lean_workbook_plus_45068
-- name    : lean_workbook_plus_45068
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/f0322344-8056-4e86-bd8d-0ec69bbb9ab5
-- statement:
--   Let the o's represent the cookies, and the l's are the symbols that divide the cookies into the three different flavors. There are six o's and the two l's. This is a total of eight items. An example of one arrangement is oolooloo, and this means that there are two of each type of cookies. We find the number of arrangements by calculating $ 8!$ and then dividing by $ 6!$ and $ 2!$ , and this gives us $ 28$ . The answer is D.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45068 :
  Nat.factorial 8 / (Nat.factorial 6 * Nat.factorial 2) = 28   :=  by sorry
