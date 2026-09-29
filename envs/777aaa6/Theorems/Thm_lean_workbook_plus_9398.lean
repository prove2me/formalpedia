-- Prove2me | Theorems.Thm_lean_workbook_plus_9398
-- name    : lean_workbook_plus_9398
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3b41b5d4-518a-4323-b81b-568856514034
-- statement:
--   Prove that if $x,y,z \in \mathbb{R}$ and $x+y+z \ge xyz$ , then $x^2+y^2+z^2 \ge xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9398 (x y z : ℝ) (h : x + y + z >= x * y * z) : x ^ 2 + y ^ 2 + z ^ 2 >= x * y * z   :=  by sorry
