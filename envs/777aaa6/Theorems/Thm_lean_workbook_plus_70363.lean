-- Prove2me | Theorems.Thm_lean_workbook_plus_70363
-- name    : lean_workbook_plus_70363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e1b0bf32-309c-4b23-b07a-5fc15f9482b3
-- statement:
--   The probability that the person selected has the disease is $ \frac{1}{100}$ . The probability that the test detects his having the disease is $ \frac{9}{10}$ . The overall probability, then, that the selected person actually has the disease AND the tests detects it is thus: $ \frac{1}{100} \bullet \frac{9}{10}=\boxed {\frac{9}{1000}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70363 :
  (1 / 100 * (9 / 10)) = (9 / 1000)   :=  by sorry
