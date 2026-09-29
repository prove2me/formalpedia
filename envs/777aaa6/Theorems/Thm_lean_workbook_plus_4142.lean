-- Prove2me | Theorems.Thm_lean_workbook_plus_4142
-- name    : lean_workbook_plus_4142
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9987b983-5be9-4921-93e3-469e7b722737
-- statement:
--   Let $(E,d)$ be a metric space. Let $f:E\to\mathbb R$ be a function such that for all $a\in\mathbb R$ the sets $X=\{x\in E:f(x)<a\}$ and $Y=\{x\in E:f(x)>a\}$ are open in $E.$ Show that $f$ is continuous.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4142 (E : Type*) [MetricSpace E] (f : E → ℝ)
    (hf : ∀ a : ℝ, IsOpen {x | f x < a} ∧ IsOpen {x | f x > a}) :
    Continuous f   :=  by sorry
