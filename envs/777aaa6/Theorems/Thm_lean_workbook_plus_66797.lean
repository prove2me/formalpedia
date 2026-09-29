-- Prove2me | Theorems.Thm_lean_workbook_plus_66797
-- name    : lean_workbook_plus_66797
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/10c181ac-8782-4460-a0bb-8cd1213dbeb6
-- statement:
--   General rule for multiplying inequalities with a sign-changing factor: $a \geq b \wedge c \geq 0 \implies ac \geq bc$, $a \geq b \wedge c \leq 0 \implies ac \leq bc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66797 (a b : ℝ) (c : ℝ) (h : a ≥ b) (h2 : c ≥ 0) : a * c ≥ b * c   :=  by sorry
