-- Prove2me | Theorems.Thm_lean_workbook_plus_51504
-- name    : lean_workbook_plus_51504
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/52f8e1ba-6666-4c32-b794-513cc45c5074
-- statement:
--   What is the value of the following expression?\n\n$$\frac{100^2-7^2}{70^2-11^2} \cdot \frac{(70-11)(70+11)}{(100-7)(100+7)}$$\n\nOptions:\n(A) 1 \n(B) $\frac{9951}{9950}$ \n(C) $\frac{4780}{4779}$ \n(D) $\frac{108}{107}$ \n(E) $\frac{81}{80}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51504 :
  ((100 ^ 2 - 7 ^ 2):ℝ) / (70 ^ 2 - 11 ^ 2) * ((70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7))) = 1   :=  by sorry
