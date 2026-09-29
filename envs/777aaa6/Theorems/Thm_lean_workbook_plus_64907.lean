-- Prove2me | Theorems.Thm_lean_workbook_plus_64907
-- name    : lean_workbook_plus_64907
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1a288dbc-a174-411a-bd9c-0d978be89a4c
-- statement:
--   $ 2(2-\sqrt{2})\sqrt{x}(\sqrt{x}-1)^2\geq 0 $ $\Leftrightarrow $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64907 : 2 * (2 - Real.sqrt 2) * Real.sqrt x * (Real.sqrt x - 1) ^ 2 ≥ 0   :=  by sorry
