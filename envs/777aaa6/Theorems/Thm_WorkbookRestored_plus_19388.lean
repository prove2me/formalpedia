-- Prove2me | Theorems.Thm_WorkbookRestored_plus_19388
-- name    : WorkbookRestored.plus_19388
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:08.461391+00:00
-- url     : https://prove2.me/theorems/6dd6a444-7045-4602-8a67-beaa34d2cf3e
-- title:
--   Lean-Workbook Plus 19388: Trigonometric identity
-- statement:
--   The sine function is odd: $\sin(-x)=-\sin x$ for every real $x$. This is the sine component of the source, which also mentions the evenness of cosine.
--
--   Source: Lean-Workbook row `lean_workbook_plus_19388` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/1d9d5b8f-be6d-457b-84bf-8db8ae251018); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_19388; immutable original Prove2Me node 1d9d5b8f-be6d-457b-84bf-8db8ae251018

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_19388 : ∀ x : ℝ, sin (-x) = -sin x   :=  by sorry
