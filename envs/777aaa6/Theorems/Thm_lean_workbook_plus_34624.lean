-- Prove2me | Theorems.Thm_lean_workbook_plus_34624
-- name    : lean_workbook_plus_34624
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/118192ce-e2ca-42d4-8a5e-e1241c325fcf
-- statement:
--   Prove that if $f(f(x))=x$ for all $x \in X$, then $f$ is both one-to-one and onto.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34624 (f : X → X) (h : ∀ x, f (f x) = x) : Function.Bijective f   :=  by sorry
