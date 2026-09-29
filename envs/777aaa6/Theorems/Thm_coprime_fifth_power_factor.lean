-- Prove2me | Theorems.Thm_coprime_fifth_power_factor
-- name    : coprime_fifth_power_factor
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T07:39:31.58471+00:00
-- url     : https://prove2.me/theorems/7b989c33-56c2-4934-964c-528cca9afc3b
-- statement:
--   If gcd(a,b)=1 and a*b=c^5, then a is a 5th power (integer). For odd n=5, the unit ambiguity is absorbed since (-d)^5 = -(d^5). Key lemma for FLT-5 Dirichlet descent.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem coprime_fifth_power_factor (a b c : ℤ) (hab : Int.gcd a b = 1) (heq : a * b = c ^ 5) : ∃ d : ℤ, a = d ^ 5 := by sorry
