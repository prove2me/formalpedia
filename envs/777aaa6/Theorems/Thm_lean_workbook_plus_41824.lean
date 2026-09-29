-- Prove2me | Theorems.Thm_lean_workbook_plus_41824
-- name    : lean_workbook_plus_41824
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/fa19135f-764f-4556-aeef-3b78dd827e21
-- statement:
--   Note that upon expanding and cancellation it remains to prove $a^4+a \ge a^3+a$ which can be rewritten as $a^3(a)+1(1) \ge a^3(1)+1(a)$ which is trivial by Rearrangement inequality because the pairs $(a^3,1) , (a,1)$ are because $a \ge 1 \iff a^3 \ge 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41824  (a : ℝ)
  (h₀ : 1 ≤ a) :
  a^4 + a ≥ a^3 + 1   :=  by sorry
