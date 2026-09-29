-- Prove2me | Theorems.Thm_WorkbookRestored_plus_41954
-- name    : WorkbookRestored.plus_41954
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:40.210604+00:00
-- url     : https://prove2.me/theorems/9d2d2970-e485-4ba3-8065-d4ff1513a939
-- title:
--   Lean-Workbook Plus 41954: Trigonometric inequality
-- statement:
--   Let positive $a,b,c$ satisfy the strict triangle inequalities, and let $A,B,C\in(0,\pi]$ obey $\cos A=(b^2+c^2-a^2)/(2bc)$ and the two cyclic cosine laws. Then $\cos A\cos B/(ab)+\cos B\cos C/(bc)+\cos A\cos C/(ac)=\sin^2A/a^2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_41954` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/81efe1ba-7212-4e89-836a-5db5c7a53331); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_41954; immutable original Prove2Me node 81efe1ba-7212-4e89-836a-5db5c7a53331

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_41954 (A B C a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) (hA: 0 < A ∧ A <= π ∧ cos A = (b^2 + c^2 - a^2)/(2*b*c))  (hB: 0 < B ∧ B <= π ∧ cos B = (a^2 + c^2 - b^2)/(2*a*c)) (hC: 0 < C ∧ C <= π ∧ cos C = (a^2 + b^2 - c^2)/(2*a*b)) : (cos A * cos B)/(a * b) + (cos B * cos C)/(b * c) + (cos A * cos C)/(a * c) = (sin A)^2/(a^2)   :=  by sorry
