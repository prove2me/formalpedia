-- Prove2me | solution 1 for lean_workbook_plus_58376
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:13.833989+00:00
-- url     : https://prove2.me/submissions/0502dc29-4c8c-473a-aa40-757cc006fb37

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℕ)
  (h₀ : Nat.gcd a b = 1) :
  Nat.gcd (a^2) (b^2) = 1 := by
  intros
  aesop (config := {maxRuleApplications := 120})
