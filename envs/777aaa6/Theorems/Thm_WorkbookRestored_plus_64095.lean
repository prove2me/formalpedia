-- Prove2me | Theorems.Thm_WorkbookRestored_plus_64095
-- name    : WorkbookRestored.plus_64095
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:34.784172+00:00
-- url     : https://prove2.me/theorems/e8404ecf-f3d6-4149-a8a6-4235110ad1b9
-- title:
--   Lean-Workbook Plus 64095: Trigonometric identity
-- statement:
--   If $x=r\cos a\cos b\cos c$, $y=r\cos a\cos b\sin c$, $z=r\sin a\cos b$, and $u=r\sin b$, then $x^2+y^2+z^2+u^2=r^2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_64095` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/b33fc46d-e32d-4614-b17c-e5033204f428); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_64095; immutable original Prove2Me node b33fc46d-e32d-4614-b17c-e5033204f428

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_64095 (x y z u r a b c : ℝ) : 
  x = r * cos a * cos b * cos c ∧ 
  y = r * cos a * cos b * sin c ∧ 
  z = r * sin a * cos b ∧ 
  u = r * sin b → 
  x^2 + y^2 + z^2 + u^2 = r^2   :=  by sorry
