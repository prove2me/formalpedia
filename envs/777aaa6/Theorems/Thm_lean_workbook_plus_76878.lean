-- Prove2me | Theorems.Thm_lean_workbook_plus_76878
-- name    : lean_workbook_plus_76878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e61ca7ea-d788-4f11-9ea0-fb4ef251ae39
-- statement:
--   Show that $n^5-n$ can be factored as $n(n^4-1)=n(n^2+1)(n^2-1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76878 : ∀ n:ℤ, n^5 - n = n * (n^4 - 1)   :=  by sorry
