-- Prove2me | Theorems.Thm_lean_workbook_plus_33810
-- name    : lean_workbook_plus_33810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/63c533f8-a960-450d-99a0-fce037a8f864
-- statement:
--   Show that $a+c$ is even if $a$ and $c$ are odd integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33810 (a c : ℤ) (h1 : Odd a) (h2 : Odd c) : Even (a + c)   :=  by sorry
