-- Prove2me | Theorems.Thm_lean_workbook_plus_10726
-- name    : lean_workbook_plus_10726
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8e07af27-8fb0-4f4f-aee1-3b764d25178d
-- statement:
--   Prove that $(p^2+1)(q^2+1) \geq (1+pq)^2$ for all real numbers $p$ and $q$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10726 (p q : ℝ) : (p^2 + 1) * (q^2 + 1) ≥ (1 + p * q)^2   :=  by sorry
