-- Prove2me | Theorems.Thm_WorkbookRestored_plus_27783
-- name    : WorkbookRestored.plus_27783
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:05.366414+00:00
-- url     : https://prove2.me/theorems/7355a912-1e90-4585-bb05-6bd525551473
-- title:
--   Lean-Workbook Plus 27783: Trigonometric identity
-- statement:
--   For every real $x$, $\sin(7x)=0$ if and only if $x=k\pi/7$ for some integer $k$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_27783` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c261f4e8-123d-4481-9e3e-4b2bfb2aabef); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_27783; immutable original Prove2Me node c261f4e8-123d-4481-9e3e-4b2bfb2aabef

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_27783 : ∀ x : ℝ, sin (7 * x) = 0 ↔ ∃ k : ℤ, x = k * π / 7   :=  by sorry
