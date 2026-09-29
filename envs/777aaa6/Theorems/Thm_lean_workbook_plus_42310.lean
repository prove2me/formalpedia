-- Prove2me | Theorems.Thm_lean_workbook_plus_42310
-- name    : lean_workbook_plus_42310
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/0d300c04-52c0-4826-948c-a47a91189f9b
-- statement:
--   A8. If $x+\frac{2}{x}=4$ , find $\frac{x^3}{2}+\frac{4}{x^3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42310 (x : ℝ) (hx : x + 2/x = 4) : x^3/2 + 4/x^3 = 20   :=  by sorry
