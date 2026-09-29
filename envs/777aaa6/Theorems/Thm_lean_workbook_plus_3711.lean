-- Prove2me | Theorems.Thm_lean_workbook_plus_3711
-- name    : lean_workbook_plus_3711
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/60e7103e-382d-4a8f-b823-6245bcc83da6
-- statement:
--   If $ f: R-> R$ and $ f(f(x))=x^2+\frac{1}{4}$ find $ f(\frac{1}{2})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3711 (f : ℝ → ℝ) (hf : ∀ x, f (f x) = x^2 + 1/4) : f (1/2) = 1/2   :=  by sorry
