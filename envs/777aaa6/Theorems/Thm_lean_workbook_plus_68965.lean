-- Prove2me | Theorems.Thm_lean_workbook_plus_68965
-- name    : lean_workbook_plus_68965
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/77c2fcad-23b1-48d3-bf2c-20526b009e42
-- statement:
--   The inequality $x+y+z-xy-xz-yz\leq 1$ is equivalent to $(1-x)(1-y)(1-z)+xyz\geq 0$ which is obvious for all $0\leq x,y,z\leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68965 (x y z : ℝ) : (x + y + z - x * y - x * z - y * z) ≤ 1 ↔ (1 - x) * (1 - y) * (1 - z) + x * y * z ≥ 0   :=  by sorry
