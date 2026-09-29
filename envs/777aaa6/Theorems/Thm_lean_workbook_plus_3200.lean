-- Prove2me | Theorems.Thm_lean_workbook_plus_3200
-- name    : lean_workbook_plus_3200
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/97cf847f-b71a-4845-ac78-882b8346df9e
-- statement:
--   Let $(X,d)$ be some metric space, and let $f : X \to X$ be a continuous function. Will the function $g : X \to \Bbb{R}$ defined by $g(x) = d(f(x),x)$ be a continuous function? If so, prove it.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3200 (X : Type) [MetricSpace X]
  (f : X → X) (hf : Continuous f) : Continuous (λ x => dist (f x) x)   :=  by sorry
