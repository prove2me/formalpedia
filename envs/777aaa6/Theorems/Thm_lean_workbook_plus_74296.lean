-- Prove2me | Theorems.Thm_lean_workbook_plus_74296
-- name    : lean_workbook_plus_74296
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9987e8a2-f5f1-414f-a40e-2f63ae7cce1a
-- statement:
--   So by Vieta's, $r+s=3$ and $rs=1$ . $r^2+s^2=(r+s)^2-2rs=3^2-2(1)=7$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74296  (r s : ℝ)
  (h₀ : r + s = 3)
  (h₁ : r * s = 1) :
  r^2 + s^2 = 7   :=  by sorry
