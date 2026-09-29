-- Prove2me | Theorems.Thm_WorkbookRestored_plus_33164
-- name    : WorkbookRestored.plus_33164
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:44.670972+00:00
-- url     : https://prove2.me/theorems/e6184fd8-8ebd-429f-b61e-6a7a963a70be
-- title:
--   Lean-Workbook Plus 33164: Trigonometric inequality
-- statement:
--   For $x\in[0,\pi]$, $(1+\sin x)\cos^2x\le32/27$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_33164` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/26b9a448-a92b-45e6-a046-bdbf266c908a); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_33164; immutable original Prove2Me node 26b9a448-a92b-45e6-a046-bdbf266c908a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_33164 : ∀ x ∈ Set.Icc 0 Real.pi, (1 + Real.sin x) * (Real.cos x)^2 ≤ 32/27   :=  by sorry
