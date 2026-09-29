-- Prove2me | solution 1 for flt7_factorization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T08:27:54.105671+00:00
-- url     : https://prove2.me/submissions/f09658f4-1c5a-414c-832b-b65b36b9d360

import Mathlib.NumberTheory.Multiplicity

-- a^7 + b^7 = (a+b) * Phi7(a,b) where Phi7 is the 7th cyclotomic polynomial evaluated at (a,b)
theorem solution (a b : ℤ) :
    a^7 + b^7 = (a + b) * (a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6) := by
  ring
