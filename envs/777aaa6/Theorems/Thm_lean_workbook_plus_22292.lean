-- Prove2me | Theorems.Thm_lean_workbook_plus_22292
-- name    : lean_workbook_plus_22292
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/cb0cc26e-5f98-42da-8f4f-1dc989cd2cea
-- statement:
--   $ 1 - \left(\frac {1}{2} + \frac {1}{2}\cdot\frac {1}{3} + \frac {1}{2}\cdot\frac {2}{3}\cdot\frac {1}{6}\right) = 1 - \frac {13}{18} = \frac {5}{18}\quad\Rightarrow\quad\mathrm{D}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22292 :
  1 - ((1 / 2 + 1 / 2 * 1 / 3 + 1 / 2 * 2 / 3 * 1 / 6) : ℚ) = 5 / 18   :=  by sorry
