-- Prove2me | Theorems.Thm_lean_workbook_plus_27287
-- name    : lean_workbook_plus_27287
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/e98b767c-99cd-4180-a37d-5f2e1b529c4f
-- statement:
--   Show that $5a-2a^2-2<1$ for $1/2<a<1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27287 (a : ℝ) (h1 : 1 / 2 < a) (h2 : a < 1) : 5 * a - 2 * a ^ 2 - 2 < 1   :=  by sorry
