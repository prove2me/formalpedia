-- Prove2me | Theorems.Thm_lean_workbook_plus_51899
-- name    : lean_workbook_plus_51899
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/c6a2446b-49ca-4426-8806-ec750f3ec405
-- statement:
--   There are two cases: \n\nCase 1: One digit is used three times, the other two digits are used once. The digits can be arranged in $ \frac {5!}{3!\times 1! \times 1!} = 20$ ways. There are three ways to choose the digit to be used three times, so this case yields $ 60$ possibilities. \n\nCase 2: Two digits are each used twice. The digits can thus be arranged in $ \frac {5!}{2! \times 2! \times 1!} = 30$ ways. There are three ways to select the digit that is only used once, so this case yields $ 90$ possibilities. \n\n$ 60 + 90 = \boxed{150}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51899 60 + 90 = 150   :=  by sorry
