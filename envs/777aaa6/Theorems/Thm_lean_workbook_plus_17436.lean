-- Prove2me | Theorems.Thm_lean_workbook_plus_17436
-- name    : lean_workbook_plus_17436
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e8d83cda-cbb0-4672-929e-6876e46331c2
-- statement:
--   If $a+4b+9c+16d=1$, $4a+9b+16c+25d=12$, $9a+16b+25c+36d=123$, find $16a+25b+36c+49d$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17436 (a b c d : ℝ) (ha : a + 4 * b + 9 * c + 16 * d = 1) (hb : 4 * a + 9 * b + 16 * c + 25 * d = 12) (hc : 9 * a + 16 * b + 25 * c + 36 * d = 123) : 16 * a + 25 * b + 36 * c + 49 * d = 334   :=  by sorry
