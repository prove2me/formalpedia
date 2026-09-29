-- Prove2me | Theorems.Thm_lean_workbook_plus_35072
-- name    : lean_workbook_plus_35072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/45423571-bcd5-4168-81e0-276ee2b429f4
-- statement:
--   Given $f(f(x))=1-x^{2}$, find the values of $f(1)$ and $f(0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35072 (f : ℝ → ℝ) (hf : ∀ x, f (f x) = 1 - x^2) : f 1 = 0 ∧ f 0 = 1   :=  by sorry
