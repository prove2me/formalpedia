-- Prove2me | Theorems.Thm_lean_workbook_plus_14183
-- name    : lean_workbook_plus_14183
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/55f9fb6b-33d0-4d4d-a580-78074293c309
-- statement:
--   $\sum\limits_{n=1}^{1999}1+\sum\limits_{n=1}^{1999}\frac{1}{a(a+1)}=1999+\frac{1999}{2000}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14183 : ∑ n in Finset.Icc 1 1999, (1 + 1 / (n * (n + 1))) = 1999 + 1999 / 2000   :=  by sorry
