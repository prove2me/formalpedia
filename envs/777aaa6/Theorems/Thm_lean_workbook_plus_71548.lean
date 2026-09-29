-- Prove2me | Theorems.Thm_lean_workbook_plus_71548
-- name    : lean_workbook_plus_71548
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/09cc06a0-d8e3-43cf-8a1e-71858b01dc40
-- statement:
--   Proof that $sin(x+y)=sin(x)cos(y)+sin(y)cos(x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71548 (x y : ℝ) : sin (x + y) = sin x * cos y + sin y * cos x   :=  by sorry
