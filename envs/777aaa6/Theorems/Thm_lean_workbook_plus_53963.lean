-- Prove2me | Theorems.Thm_lean_workbook_plus_53963
-- name    : lean_workbook_plus_53963
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/aed3e272-082f-477a-ac9e-07feca755eee
-- statement:
--   From $2 \geq |x + y + z - xyz|$, prove that $2 + xyz \geq x + y + z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53963 (x y z : ℝ) : 2 ≥ |x + y + z - xyz| → 2 + xyz ≥ x + y + z   :=  by sorry
