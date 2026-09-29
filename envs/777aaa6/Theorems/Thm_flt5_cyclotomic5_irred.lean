-- Prove2me | Theorems.Thm_flt5_cyclotomic5_irred
-- name    : flt5_cyclotomic5_irred
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T10:59:21.991182+00:00
-- url     : https://prove2.me/theorems/b581617e-ce9f-406b-9841-5a715ea8c054
-- statement:
--   The 5th cyclotomic polynomial is irreducible over ℚ. For prime p, cyclotomic p is irreducible over ℚ by the Eisenstein criterion applied via X→X+1 substitution (giving Eisenstein at p).

import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Data.Int.Basic

theorem flt5_cyclotomic5_irred : Irreducible (Polynomial.cyclotomic 5 ℚ) := by sorry
