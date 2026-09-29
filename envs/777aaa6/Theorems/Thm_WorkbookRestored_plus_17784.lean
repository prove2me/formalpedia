-- Prove2me | Theorems.Thm_WorkbookRestored_plus_17784
-- name    : WorkbookRestored.plus_17784
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:00.42414+00:00
-- url     : https://prove2.me/theorems/981114b9-e390-468e-9fc2-bacca8a0f021
-- title:
--   Lean-Workbook Plus 17784: Trigonometric identity
-- statement:
--   The function $f(x)=\sin x/(1+x^4)$ is odd: $f(-x)=-f(x)$ for every real $x$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_17784` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/d07fb2cb-fccc-4c62-8695-7b87ffb754a4); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_17784; immutable original Prove2Me node d07fb2cb-fccc-4c62-8695-7b87ffb754a4

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_17784 (f : ℝ → ℝ) (f_def : ∀ x, f x = sin x / (1 + x ^ 4)) : ∀ x, f (-x) = -f x   :=  by sorry
