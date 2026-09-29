-- Prove2me | Theorems.Thm_lean_workbook_plus_3721
-- name    : lean_workbook_plus_3721
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/53c61072-3365-474c-9a7b-ef7952d051b9
-- statement:
--   Let $f : X \to X$ be such that $d(f(x),f(y)) \le a d(x,y)$ for every $x,y \in X$ for some $a \in (0,1)$ . Show that $g(x) = d(f(x),x)$ is continuous.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3721 (X : Type*) [MetricSpace X]
  (α : ℝ) (hα : 0 < α ∧ α < 1) (f : X → X) (hf : ∀ x y, dist (f x) (f y) ≤ α * dist x y) :
  Continuous (λ x => dist (f x) x)   :=  by sorry
