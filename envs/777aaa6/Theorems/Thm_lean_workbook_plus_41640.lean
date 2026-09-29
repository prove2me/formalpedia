-- Prove2me | Theorems.Thm_lean_workbook_plus_41640
-- name    : lean_workbook_plus_41640
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2a01466e-c461-4800-8db3-81624af9689c
-- statement:
--   $ \underbrace{\left(\binom{2n}{2}-2n\right)}_{\text{diagonals of a regular polygon of} \ 2n \ \text{sides}}-\underbrace{n}_{\text{not through the center of the circle to the polygon}}$ \n \n $ = \boxed{2n(n-2)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41640 (Nat.choose (2 * n) 2 - 2 * n) - n = 2 * n * (n - 2)   :=  by sorry
