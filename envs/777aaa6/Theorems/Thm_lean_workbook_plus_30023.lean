-- Prove2me | Theorems.Thm_lean_workbook_plus_30023
-- name    : lean_workbook_plus_30023
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/522e1827-bf6b-4595-8f5e-7d64878f381b
-- statement:
--   If $\alpha$ is a complex number such that $\textrm{Re}\alpha<\frac{19}{2}$, then $\left| 10-\alpha\right| >\left| 9-\alpha\right|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30023 : ∀ α : ℂ, (Complex.re α < 19 / 2 → Complex.abs (10 - α) > Complex.abs (9 - α))   :=  by sorry
