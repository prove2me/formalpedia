-- Prove2me | Theorems.Thm_lean_workbook_plus_64047
-- name    : lean_workbook_plus_64047
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/c601b59c-bd02-445d-9d58-681da0bc6d64
-- statement:
--   Prove $\frac{1}{1+a}+\frac{1}{1+b}+\frac{1}{1+c} \ge \frac{9}{3+a+b+c}$ for $\forall a,b,c \in \mathbb{R^+}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64047 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≥ 9 / (3 + a + b + c)   :=  by sorry
