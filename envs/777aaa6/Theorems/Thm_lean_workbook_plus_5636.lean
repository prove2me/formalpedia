-- Prove2me | Theorems.Thm_lean_workbook_plus_5636
-- name    : lean_workbook_plus_5636
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e7a2dd95-8da2-48a1-9c74-70fc43cb1b1a
-- statement:
--   Suppose you have 10 blank digits, you have to take 2 positions for the two 2's. THen that is 10 taken two at a time which is $ \binom{10}{2}$ . The remaining 8 positions, can only take 1 and 3. That is for each position, you have 2 choices. That is $ 2^{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5636 :
  Nat.choose 10 2 * 2^8 = 10! / 8! * 2^8   :=  by sorry
