-- Prove2me | Theorems.Thm_lean_workbook_plus_14944
-- name    : lean_workbook_plus_14944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b4d85161-ed1e-4529-bf86-0744c4fdb9eb
-- statement:
--   Prove: $3t+\frac{1}{t}\geq 4$ for $t\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14944 (t : ℝ) (ht: t >= 1): 3 * t + 1 / t ≥ 4   :=  by sorry
