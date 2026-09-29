-- Prove2me | Theorems.Thm_lean_workbook_plus_31883
-- name    : lean_workbook_plus_31883
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/5a7b88e9-5be7-488b-baa6-bfc27e0f606c
-- statement:
--   Now what we need to prove is just $(1+t)^2 \ge 12(t-2)$ , or $t^2-10t+25 \ge 0$ , which is just $(t-5)^2 \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31883 : ∀ t : ℝ, (1 + t) ^ 2 ≥ 12 * (t - 2)   :=  by sorry
