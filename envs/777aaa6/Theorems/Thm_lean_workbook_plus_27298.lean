-- Prove2me | Theorems.Thm_lean_workbook_plus_27298
-- name    : lean_workbook_plus_27298
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/aad061dc-7aaf-49e3-834a-eeb681515e39
-- statement:
--   Prove that if a function $f(x)$ is symmetric about $x=b$, then $g(f(x))$ is also symmetric about $x=b$ for any function $g(x)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27298 (f g : ℝ → ℝ) (b : ℝ) (hf : ∀ x, f (b + x) = f (b - x)) (hg : ∀ x, g (f (b + x)) = g (f (b - x))) : ∀ x, g (f (b + x)) = g (f (b - x))   :=  by sorry
