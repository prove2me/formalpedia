-- Prove2me | Theorems.Thm_lean_workbook_plus_11432
-- name    : lean_workbook_plus_11432
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/382aaa56-a8ae-453c-bf89-3eb528fde2ae
-- statement:
--   Let us first deal with $a$ and $b$ . We know that $\gcd(a, b) * \operatorname{lcm}(a, b) = ab \implies ab = 2 * 30 = 60$ . Guess and check leads to $30$ and $2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11432  (a b : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : Nat.lcm a b = 30)
  (h₂ : Nat.gcd a b = 2) :
  a * b = 60   :=  by sorry
