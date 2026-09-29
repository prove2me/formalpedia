-- Prove2me | Theorems.Thm_lean_workbook_plus_14036
-- name    : lean_workbook_plus_14036
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/59e155fd-6f24-48fd-9e5e-bdbb4287c20a
-- statement:
--   Let $ a,b,c\in[\frac{1}{2},1]$ . Prove that $ ab+bc+ca+\frac{3}{4} \geq a+b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14036 (a b c : ℝ) (ha : a ∈ Set.Icc (1 / 2) 1) (hb : b ∈ Set.Icc (1 / 2) 1) (hc : c ∈ Set.Icc (1 / 2) 1) : a * b + b * c + c * a + 3 / 4 ≥ a + b + c   :=  by sorry
