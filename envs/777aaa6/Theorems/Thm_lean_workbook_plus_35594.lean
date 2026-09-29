-- Prove2me | Theorems.Thm_lean_workbook_plus_35594
-- name    : lean_workbook_plus_35594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/4450ff8b-d5b8-411b-b0f5-d38862e05edc
-- statement:
--   prove $\forall k\in [p^2,(p+1)^2)$ : $\lfloor\sqrt k\rfloor=p$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35594 (p : ℕ) (k : ℕ) (h₁ : p * p ≤ k) (h₂ : k < (p + 1) * (p + 1)) : ⌊Real.sqrt k⌋ = p   :=  by sorry
