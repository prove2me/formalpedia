-- Prove2me | Theorems.Thm_WorkbookRestored_plus_38068
-- name    : WorkbookRestored.plus_38068
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:35:14.310671+00:00
-- url     : https://prove2.me/theorems/86c9c743-102c-4913-953b-b835eb15d19c
-- title:
--   Lean-Workbook Plus 38068: Trigonometric inequality
-- statement:
--   **Lean-Workbook Plus 38068: Real power of a power**
--
--   For real $x\ge0$ and real $a,b$, $x^{ab}=(x^a)^b$. The formal statement uses Lean’s total real-power convention at base zero.
--
--   Source: Lean-Workbook row `lean_workbook_plus_38068` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6216b4dc-ed49-4a89-a143-b8060dccabdf); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_38068; immutable original Prove2Me node 6216b4dc-ed49-4a89-a143-b8060dccabdf

import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem WorkbookRestored.plus_38068 {x : ℝ} (hx : 0 ≤ x) (a b : ℝ) : x ^ (a * b) = (x ^ a) ^ b   :=  by sorry
