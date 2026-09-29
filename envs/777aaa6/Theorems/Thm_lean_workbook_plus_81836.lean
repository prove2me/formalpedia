-- Prove2me | Theorems.Thm_lean_workbook_plus_81836
-- name    : lean_workbook_plus_81836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/5526f3f8-1493-47fc-8aba-747bec265909
-- statement:
--   But $\mid x_1\mid+...+\mid x_n\mid \geq \mid x_1+...+x_n\mid$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81836 (n : ℕ) (x : Fin n → ℝ) :
  ∑ i, ‖x i‖ ≥ ‖∑ i, x i‖   :=  by sorry
