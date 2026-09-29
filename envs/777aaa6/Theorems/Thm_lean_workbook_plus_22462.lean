-- Prove2me | Theorems.Thm_lean_workbook_plus_22462
-- name    : lean_workbook_plus_22462
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8e5ff7cc-f177-48ac-b8d1-347453148cad
-- statement:
--   $ \cos 27^\circ = \sqrt {\frac {1 + \sin 36^\circ}{2}} = \sqrt {\frac {1 + \sqrt {1 - \cos ^ 2 36^\circ}}{2}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22462 : Real.cos (27 * Real.pi / 180) = Real.sqrt ((1 + Real.sin (36 * Real.pi / 180)) / 2)   :=  by sorry
