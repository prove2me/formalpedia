-- Prove2me | Theorems.Thm_WorkbookRestored_plus_44804
-- name    : WorkbookRestored.plus_44804
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:02.382537+00:00
-- url     : https://prove2.me/theorems/0e80d03f-3590-4c1b-a9fd-42bf11568356
-- title:
--   Lean-Workbook Plus 44804: Trigonometric identity
-- statement:
--   The map $t\mapsto(\cos t,\sin t)$ from $\mathbb R$ to $\mathbb R^2$ is continuous.
--
--   Source: Lean-Workbook row `lean_workbook_plus_44804` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/7c8334d2-212d-4efb-9ba8-eaa2c7ca1263); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_44804; immutable original Prove2Me node 7c8334d2-212d-4efb-9ba8-eaa2c7ca1263

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_44804 : Continuous fun t => (cos t, sin t)   :=  by sorry
