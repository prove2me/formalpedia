-- Prove2me | Theorems.Thm_lean_workbook_plus_16641
-- name    : lean_workbook_plus_16641
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/48ae82da-693e-4d92-b488-37429bcc47e0
-- statement:
--   By AM-GM inequality,\n $x^6z^2+y^6x^2\geq 2x^4y^3z$ \n $\rightarrow$ \n $6\sum_{cyc}x^6z^2\geq 6\sum_{cyc}x^4y^3z$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16641 (x y z : ℝ) :
  6 * (x ^ 6 * z ^ 2 + y ^ 6 * x ^ 2 + z ^ 6 * y ^ 2) ≥ 6 * (x ^ 4 * y ^ 3 * z + y ^ 4 * z ^ 3 * x + z ^ 4 * x ^ 3 * y)   :=  by sorry
