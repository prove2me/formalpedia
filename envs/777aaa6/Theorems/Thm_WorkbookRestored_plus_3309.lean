-- Prove2me | Theorems.Thm_WorkbookRestored_plus_3309
-- name    : WorkbookRestored.plus_3309
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:43:28.965053+00:00
-- url     : https://prove2.me/theorems/4f10ba09-f5b5-4b87-b07c-b3630277438b
-- title:
--   A product of four successive real exponents
-- statement:
--   Let $a,b,c,d$ be real numbers satisfying $4^a=5$, $5^b=6$, $6^c=7$, and $7^d=8$. Then $$abcd=\frac32.$$
--
--   This restores the missing imports or namespaces of [the original node](https://prove2.me/theorems/4ecbede2-e1ae-48fd-8918-9af11144d4de), retaining its formal proposition. Source: Lean-Workbook row `lean_workbook_plus_3309` (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_3309; original Prove2Me node 4ecbede2-e1ae-48fd-8918-9af11144d4de; Apache-2.0

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_3309 (a b c d : ℝ) (h1 : (4:ℝ)^a = 5) (h2 : (5:ℝ)^b = 6) (h3 : (6:ℝ)^c = 7) (h4 : (7:ℝ)^d = 8) : a*b*c*d = 3/2   :=  by sorry
