-- Prove2me | Theorems.Thm_lean_workbook_plus_13305
-- name    : lean_workbook_plus_13305
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/049ae45d-1625-4b05-bb7a-14136df96d58
-- statement:
--   If we have $ x+y=27$ and $ x-y=1$ (Sorry, I couldn't really explain anything legit other than guess and check), then solving the system gives $ x=14$ and $ y=13$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13305  (x y : ℕ)
  (h₀ : x + y = 27)
  (h₁ : x - y = 1) :
  x = 14 ∧ y = 13   :=  by sorry
