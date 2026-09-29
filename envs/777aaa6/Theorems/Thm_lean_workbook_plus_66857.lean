-- Prove2me | Theorems.Thm_lean_workbook_plus_66857
-- name    : lean_workbook_plus_66857
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3a721e2e-069f-47c9-bdc8-9e0a1d002316
-- statement:
--   Prove that if $f$ is an automorphism on Z, then $f(1)$ must be either 1 or -1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66857 (f : ℤ ≃+* ℤ) : f 1 = 1 ∨ f 1 = -1   :=  by sorry
