-- Prove2me | Theorems.Thm_lean_workbook_plus_5259
-- name    : lean_workbook_plus_5259
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1b980a98-e02a-4161-b217-7900854370f7
-- statement:
--   I'm not sure that you are understanding my solution. The trivial inequality states that for any $a \in \mathbb{R}$ , $a^2 \ge 0$ , with equality at $a = 0$ . Using this with $x-2$ and $y+1$ , we obtain the inequalities $(x-2)^2 \ge 0$ and $(y+1)^2\ge 0$ . Therefore $$(x-2)^2 + 3 \ge 3$$ and $$(y+1)^2 + 5 \ge 5.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5259  (x y : ℝ) :
  (x - 2)^2 + 3 ≥ 3 ∧ (y + 1)^2 + 5 ≥ 5   :=  by sorry
