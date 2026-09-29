-- Prove2me | Theorems.Thm_lean_workbook_plus_19550
-- name    : lean_workbook_plus_19550
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/736b0d81-ccf3-460f-8b3d-ac133b64f4a3
-- statement:
--   Show that the expression $(u^3-\sqrt3u^2v-(3-\sqrt3)uv^2+v^3)^2$ is non-negative
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19550 (u v : ℝ) : (u^3 - Real.sqrt 3 * u^2 * v - (3 - Real.sqrt 3) * u * v^2 + v^3)^2 ≥ 0   :=  by sorry
