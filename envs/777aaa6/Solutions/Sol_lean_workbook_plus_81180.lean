-- Prove2me | solution 1 for lean_workbook_plus_81180
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:56.713156+00:00
-- url     : https://prove2.me/submissions/9aedda06-e5f7-4660-b4c9-cf6b415ed7a6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.Equiv.Basic

open scoped BigOperators

theorem solution (G : Type*) [Fintype G] [CommGroup G] (f : G → ℂ) (h : G) :
    ∑ g : G, f g = ∑ g : G, f (h*g) := by
  simpa using (Equiv.sum_comp (Equiv.mulLeft h) f).symm
