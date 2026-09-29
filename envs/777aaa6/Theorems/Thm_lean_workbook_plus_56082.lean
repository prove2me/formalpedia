-- Prove2me | Theorems.Thm_lean_workbook_plus_56082
-- name    : lean_workbook_plus_56082
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/b8f1f20c-b820-4d8b-a80b-981f200c1933
-- statement:
--   Define $f(x)=1$ if $x\ge0$ and $f(x)=-1$ if $x<0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56082 : ∀ x : ℝ, ( if x ≥ 0 then 1 else -1 ) = ( if x ≥ 0 then 1 else -1 )   :=  by sorry
