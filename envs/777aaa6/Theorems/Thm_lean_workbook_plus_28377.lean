-- Prove2me | Theorems.Thm_lean_workbook_plus_28377
-- name    : lean_workbook_plus_28377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/c09e27c6-c9b9-4a72-be79-b9560cf3fc38
-- statement:
--   Let $g, h \colon \mathbb{R} \to \mathbb{R}$ both continuous at $a$, with $g(a)=h(a) = b$. Let $f \colon \mathbb{R} \to \mathbb{R}$ be defined by $f(x) = g(x)$ if $x \in \mathbb{Q}$ and $f(x) = h(x)$ if $x \not \in \mathbb{Q}$. Then $f$ is continuous at $a$ (where it takes value $b$).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28377  {g h f : ℝ → ℝ} {a b : ℝ} (hg : ContinuousAt g a) (hh : ContinuousAt h a) (hg' : g a = b) (hh' : h a = b)
  (hf : ∀ x, (x ∈ Set.range ((↑) : ℚ → ℝ) ↔ f x = g x) ∧ (x ∉ Set.range ((↑) : ℚ → ℝ) ↔ f x = h x)) :
  ContinuousAt f a   :=  by sorry
