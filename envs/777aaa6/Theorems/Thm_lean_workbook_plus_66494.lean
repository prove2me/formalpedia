-- Prove2me | Theorems.Thm_lean_workbook_plus_66494
-- name    : lean_workbook_plus_66494
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6a80f5a3-653f-4321-9b7e-ce2c3cece4fc
-- statement:
--   Prove $(rs)^2+(st)^2+(rt)^2\geq (r+s+t)(rst)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66494 (r s t : ℝ) : (r * s) ^ 2 + (s * t) ^ 2 + (r * t) ^ 2 ≥ (r + s + t) * (r * s * t)   :=  by sorry
