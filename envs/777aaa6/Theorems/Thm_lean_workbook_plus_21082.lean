-- Prove2me | Theorems.Thm_lean_workbook_plus_21082
-- name    : lean_workbook_plus_21082
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/95a437be-2ce3-4a3c-b4b5-2934b988571e
-- statement:
--   Now by Cauchy Schwarz inequality $ (\sum_{cyc} a^2 )( 1+1+1 ) \geq ( \sum_{cyc} a )^2 = 1 \Rightarrow \sum_{cyc} a^2 \geq \frac{1}{3} \ \cdots (1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21082  (a b c : ℝ)
  (h₀ : a + b + c = 1) :
  a^2 + b^2 + c^2 ≥ 1 / 3   :=  by sorry
