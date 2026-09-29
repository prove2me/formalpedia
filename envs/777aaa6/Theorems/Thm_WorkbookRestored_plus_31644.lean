-- Prove2me | Theorems.Thm_WorkbookRestored_plus_31644
-- name    : WorkbookRestored.plus_31644
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:31.569979+00:00
-- url     : https://prove2.me/theorems/8ed48adb-e479-44a6-b9fb-579fd2af3448
-- title:
--   Lean-Workbook Plus 31644: Trigonometric identity
-- statement:
--   For every real $\theta$, $\cos\theta+\sqrt3\sin\theta=2(\cos\theta\cos(\pi/3)+\sin\theta\sin(\pi/3))$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_31644` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c59da304-be92-48d5-9172-ad8d266b3c2c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_31644; immutable original Prove2Me node c59da304-be92-48d5-9172-ad8d266b3c2c

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_31644 (θ : ℝ) :
  Real.cos θ + Real.sqrt 3 * Real.sin θ =
    2 * (Real.cos θ * Real.cos (Real.pi / 3) + Real.sin θ * Real.sin (Real.pi / 3))   :=  by sorry
