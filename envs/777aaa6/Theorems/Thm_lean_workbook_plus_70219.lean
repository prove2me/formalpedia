-- Prove2me | Theorems.Thm_lean_workbook_plus_70219
-- name    : lean_workbook_plus_70219
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a3b120c5-dec4-44ce-b7de-7f8b484f53dd
-- statement:
--   (1) $ \left(\frac {1}{2}\right)^2*\left\{_6 C_3\left(\frac {1}{2}\right)^3\left(\frac {1}{2}\right)^2 + _6 C_1\left(\frac {1}{2}\right)*\left(\frac {1}{2}\right)^5\right\} = \frac {13}{128}$ \n\n(2) $ \left\{_4 C_2\left(\frac {1}{2}\right)^2\left(\frac {1}{2}\right)^2\right\}*_4 C_1\left(\frac {1}{2}\right)*\left(\frac {1}{2}\right)^3=\frac{3}{32}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70219 :
  ((1 / 2)^2 * (6! / (3! * 2!) * (1 / 2)^3 * (1 / 2)^2 + 6! / (1! * 5!) * (1 / 2) * (1 / 2)^5)) = 13 / 128 ∧
  ((4! / (2! * 2!) * (1 / 2)^2 * (1 / 2)^2) * (4! / (1! * 3!) * (1 / 2) * (1 / 2)^3)) = 3 / 32   :=  by sorry
