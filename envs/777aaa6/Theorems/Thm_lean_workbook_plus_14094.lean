-- Prove2me | Theorems.Thm_lean_workbook_plus_14094
-- name    : lean_workbook_plus_14094
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9ac9c7e7-50cb-4d16-96f5-3d09a40e6aa7
-- statement:
--   Prove that for each of the $(1+2x)$ consecutive integers $i$ such that $x^2 \le i < (x+1)^2 $ we have $\lfloor\sqrt{i}\rfloor=x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14094 (x : ℕ) (i : ℕ) (hi : x^2 ≤ i ∧ i < (x + 1)^2) : ⌊Real.sqrt i⌋ = x   :=  by sorry
