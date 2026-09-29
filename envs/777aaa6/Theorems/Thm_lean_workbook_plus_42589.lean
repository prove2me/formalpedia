-- Prove2me | Theorems.Thm_lean_workbook_plus_42589
-- name    : lean_workbook_plus_42589
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/55c63ba1-9300-42f3-8b89-b1b370bc62a8
-- statement:
--   Therefore, the probability is $ \frac{21!17!5!}{22!17!4!}=\boxed{\frac{5}{22}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42589 : (factorial 21 * factorial 17 * factorial 5) / (factorial 22 * factorial 17 * factorial 4) = 5/22   :=  by sorry
