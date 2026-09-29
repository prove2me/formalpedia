-- Prove2me | Theorems.Thm_WorkbookRestored_plus_4590
-- name    : WorkbookRestored.plus_4590
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:28:56.988426+00:00
-- url     : https://prove2.me/theorems/cd21d101-1e55-4a2a-bffc-71a33b061961
-- title:
--   Lean-Workbook Plus 4590: Trigonometric identity
-- statement:
--   Express $\sqrt{2}$ in terms of cosine: $\sqrt{2} = 2\cos\left(\frac{\pi}{4}\right)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_4590` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/918ebac2-c413-409a-9114-2b8bed189d76); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_4590; immutable original Prove2Me node 918ebac2-c413-409a-9114-2b8bed189d76

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_4590 : 2 * Real.cos (Real.pi / 4) = Real.sqrt 2   :=  by sorry
