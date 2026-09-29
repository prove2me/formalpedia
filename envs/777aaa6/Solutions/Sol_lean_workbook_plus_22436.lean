-- Prove2me | solution 1 for lean_workbook_plus_22436
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:41.201078+00:00
-- url     : https://prove2.me/submissions/8eeaac5c-55c2-41f1-8a51-b7ccf9dc9752

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b d : ℤ) (hd : d = gcd a b) : ∃ x y : ℤ, a * x + b * y = d := by
  subst d
  exact ⟨Int.gcdA a b, Int.gcdB a b, (Int.gcd_eq_gcd_ab a b).symm⟩
