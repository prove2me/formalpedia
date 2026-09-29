-- Prove2me | Theorems.Thm_lean_workbook_plus_43578
-- name    : lean_workbook_plus_43578
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/07572fb2-c0eb-416b-8cdf-cc7ab4f54b9e
-- statement:
--   The average of $a,b$ and $c$ is $8$ less than $d.$ If the average of $a,b,c$ and $d$ is $42,$ then what is the average of $(3d-2)$ and $(d+5)?$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43578 (a b c d : ℝ) : (a + b + c) / 3 = d - 8 ∧ (a + b + c + d) / 4 = 42 → (3 * d - 2 + d + 5) / 2 = 97.5   :=  by sorry
