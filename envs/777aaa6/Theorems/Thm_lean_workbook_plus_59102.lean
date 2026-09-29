-- Prove2me | Theorems.Thm_lean_workbook_plus_59102
-- name    : lean_workbook_plus_59102
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d172544e-bda4-4feb-8010-35deb2038456
-- statement:
--   The following inequality a bit of stronger: \n $$2\left(\frac{1}{sin \alpha}+\frac{1}{sin \beta}+\frac{1}{sin \gamma}\right)- \frac{sin\alpha}{sin \beta sin \gamma}-\frac{sin\beta}{sin \alpha sin \gamma}-\frac{sin\gamma}{sin \alpha sin \beta}\geq2\sqrt3.$$ \n \n After's Ravi's substitution it's equivalent to $xy+yz+zx\geq \sqrt{3xyz(x+y+z)}$ , which is true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59102 :
  ∀ α β γ : ℝ, 2 * (1 / Real.sin α + 1 / Real.sin β + 1 / Real.sin γ) - Real.sin α / (Real.sin β * Real.sin γ) - Real.sin β / (Real.sin α * Real.sin γ) - Real.sin γ / (Real.sin α * Real.sin β) ≥ 2 * Real.sqrt 3   :=  by sorry
