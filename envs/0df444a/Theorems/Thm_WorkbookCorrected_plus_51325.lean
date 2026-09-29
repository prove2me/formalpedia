-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_51325
-- name    : WorkbookCorrected.plus_51325
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T15:15:51.126854+00:00
-- url     : https://prove2.me/theorems/4c1976f9-0867-4303-810b-5b0730bcb92a
-- title:
--   Failure of uniform convergence for a growing narrow spike
-- statement:
--   For n ≥ 1, define fₙ(x)=√n on 0 ≤ x ≤ 1/n and fₙ(x)=0 on 1/n < x ≤ 1. The sequence has no uniform limit on [0,1].
--
--   Formalization Note: States nonexistence of any uniform limit function as requested, rather than merely failure of uniform convergence to zero.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_51325 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_51325; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_51325 (f : ℕ → ℝ → ℝ)
    (hf : ∀ n : ℕ, ∀ x : ℝ, f n x=if 0 ≤ x ∧ x ≤ 1/(n:ℝ) then Real.sqrt n else 0) :
    ¬ ∃ g : ℝ → ℝ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N < n →
      ∀ x ∈ Set.Icc (0:ℝ) 1, |f n x-g x| < ε := by sorry
