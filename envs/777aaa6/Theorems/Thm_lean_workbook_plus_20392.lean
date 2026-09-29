-- Prove2me | Theorems.Thm_lean_workbook_plus_20392
-- name    : lean_workbook_plus_20392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/acb63c2f-5630-4035-925b-b324cfaea719
-- statement:
--   There are $\frac{240}{4} = 60$ multiples of $4$, and $\frac{240}{6} = 40$ multiples of $6$. For a number to be a multiple of both $4$ and $6$, it must be a multiple of $12$, as $12$ is the LCM of $4$ and $6$. Therefore, there are $\frac{240}{12} = 20$ multiples of both $4$ and $6$. By PIE, there are $60 + 40 - 20 = \boxed{80}$ multiples of either $4$ or $6$ (or both).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20392 :
  Finset.card (Finset.filter (λ x => 4 ∣ x ∨ 6 ∣ x) (Finset.range 240)) = 80   :=  by sorry
