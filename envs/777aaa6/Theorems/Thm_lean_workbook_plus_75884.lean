-- Prove2me | Theorems.Thm_lean_workbook_plus_75884
-- name    : lean_workbook_plus_75884
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9bbac5a4-b536-4800-8fe8-aec53deb869f
-- statement:
--   $ \frac {1}{2} \cdot \frac {3}{4} \cdot \frac {5}{6} \cdot ... \cdot \frac {1997}{1998}>\frac {1}{3} \cdot \frac {3}{5} \cdot \frac {5}{7} \cdot ... \cdot \frac {1997}{1999}=\frac{1}{1999}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75884 : (∏ i in Finset.Icc 1 1997, (2 * i + 1) / (2 * i + 2)) > (∏ i in Finset.Icc 1 1997, (2 * i + 1) / (2 * i + 3))   :=  by sorry
