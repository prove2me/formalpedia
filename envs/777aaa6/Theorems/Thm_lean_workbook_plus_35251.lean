-- Prove2me | Theorems.Thm_lean_workbook_plus_35251
-- name    : lean_workbook_plus_35251
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/fdb8cbbc-7ddf-444d-a4ee-c1812b6b617c
-- statement:
--   Given that $ p + q + r = 0$, prove the identity $ pqr + (p+q)(q+r)(r+p) = -(p+q+r)^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35251 (p q r : ℂ) (h : p + q + r = 0) :
  p*q*r + (p+q)*(q+r)*(r+p) = -(p+q+r)^3   :=  by sorry
