-- Prove2me | Theorems.Thm_lean_workbook_plus_44828
-- name    : lean_workbook_plus_44828
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/9b38f488-b5ee-4f79-9074-ffdefa434bf1
-- statement:
--   If $ a,b,c \ge 1$ then $ 4(abc+1)\ge (1+a)(1+b)(1+c)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44828 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : 4 * (a * b * c + 1) ≥ (1 + a) * (1 + b) * (1 + c)   :=  by sorry
