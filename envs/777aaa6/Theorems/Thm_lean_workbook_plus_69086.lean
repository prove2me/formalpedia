-- Prove2me | Theorems.Thm_lean_workbook_plus_69086
-- name    : lean_workbook_plus_69086
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/fe69013a-63e8-4675-9ab2-ee9531bbb856
-- statement:
--   Prove that $\text{lcm}[a_k,a_{k+1}] = \frac {a_k a_{k+1}} {\gcd(a_k,a_{k+1})}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69086 {a b : ℕ} : Nat.lcm a b = a * b / Nat.gcd a b   :=  by sorry
