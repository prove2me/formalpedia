-- Prove2me | Theorems.Thm_lean_workbook_plus_50601
-- name    : lean_workbook_plus_50601
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/fccb23f5-8fe4-4501-a9fb-b4297930c5dd
-- statement:
--   Prove that $\frac{\left | a-b \right |}{1+\left | a-b \right |}\leq \frac{\left | a \right |}{1+\left | a \right |}+\frac{\left | b \right |}{1+\left | b \right |}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50601 (a b : ℝ) :  |a - b| / (1 + |a - b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|)   :=  by sorry
