-- Prove2me | Theorems.Thm_lean_workbook_plus_51476
-- name    : lean_workbook_plus_51476
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/735c227d-8eb0-4311-9358-d6c12dedebcc
-- statement:
--   If a $\neq$ 0,then $(a^{-1})^{-1}$ = a ; also if a $\neq$ 0 and b $\neq$ 0, then $(ab)^{-1}= a^{-1} b^{-1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51476 (a : ℝ) (h : a ≠ 0) : (a⁻¹)⁻¹ = a   :=  by sorry
