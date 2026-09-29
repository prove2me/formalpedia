-- Prove2me | Theorems.Thm_lean_workbook_plus_54565
-- name    : lean_workbook_plus_54565
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/216b1217-f6f1-46e5-ac53-68c0afa96f9e
-- statement:
--   Let $f, g : \mathbb R \to \mathbb R$ be two functions such that $g\circ f : \mathbb R \to \mathbb R$ is an injective function. Prove that $f$ is also injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54565 (f g : ℝ → ℝ) (hg : Function.Injective g) (hgf : Function.Injective (g ∘ f)) : Function.Injective f   :=  by sorry
