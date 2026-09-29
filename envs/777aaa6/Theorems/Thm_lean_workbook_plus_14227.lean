-- Prove2me | Theorems.Thm_lean_workbook_plus_14227
-- name    : lean_workbook_plus_14227
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b69cff19-623c-4423-8866-ca017da67e0a
-- statement:
--   $P(x,0)$ $\implies$ $f(xf(x))=x^2$ (note that this implies $f(u)=0$ $\implies$ $u=0$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14227 (f : ℝ → ℝ) (hf : ∀ x, f (x * f x) = x ^ 2) : ∀ x, f x = 0 ↔ x = 0   :=  by sorry
