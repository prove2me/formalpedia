-- Prove2me | Theorems.Thm_lean_workbook_plus_34950
-- name    : lean_workbook_plus_34950
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1f1404db-6f6c-49b9-8b51-5a60308e612d
-- statement:
--   2) Let $a>0$ and $t\ge 0$ , then : $f(x)=1-(1-x)^t$ $\forall x<1$ $f(1)=1$ $f(x)=1+a(x-1)^t$ $\forall x>1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34950 (a t : ℝ) (f : ℝ → ℝ) (hf: f = fun x => if x < 1 then 1 - (1 - x) ^ t else if x = 1 then 1 else 1 + a * (x - 1) ^ t) : a > 0 ∧ t >= 0 → ∀ x < 1, f x = 1 - (1 - x) ^ t ∧ ∀ x > 1, f x = 1 + a * (x - 1) ^ t   :=  by sorry
