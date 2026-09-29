-- Prove2me | Theorems.Thm_lean_workbook_plus_72938
-- name    : lean_workbook_plus_72938
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/64508c30-61a0-4bb8-b2b8-d24cae4051fc
-- statement:
--   Given $p\in\mathbb{R}$ and $p^2=1+p$ , prove that $p^3=1+2p$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72938 (p : ℝ) (h : p^2 = 1 + p) : p^3 = 1 + 2 * p   :=  by sorry
