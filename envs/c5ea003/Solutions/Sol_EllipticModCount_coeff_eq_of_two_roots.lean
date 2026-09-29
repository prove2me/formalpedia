-- Prove2me | solution 1 for EllipticModCount.coeff_eq_of_two_roots
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:52:41.029053+00:00
-- url     : https://prove2.me/submissions/372e4d04-fd99-4dc7-9aec-71f246aa6e24

import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount

open EllipticModCount

variable {F : Type*} [Field F]
variable {a b r s : F}

theorem solution (hr : wRHS a b r = 0) (hs : wRHS a b s = 0) (hrs : r ≠ s) :
    a = -(r ^ 2 + r * s + s ^ 2) ∧ b = r * s * (r + s) := by
  simp only [wRHS] at hr hs
  -- r³ + a r + b = 0, s³ + a s + b = 0
  have hdiff : r ^ 3 - s ^ 3 + a * (r - s) = 0 := by
    linear_combination hr - hs
  have hfactor : r ^ 3 - s ^ 3 = (r - s) * (r ^ 2 + r * s + s ^ 2) := by ring
  have hdiff' : (r - s) * (r ^ 2 + r * s + s ^ 2 + a) = 0 := by
    rw [hfactor] at hdiff
    convert hdiff using 1
    ring
  have hne : r - s ≠ 0 := sub_ne_zero.mpr hrs
  have ha' : r ^ 2 + r * s + s ^ 2 + a = 0 := by
    exact (mul_eq_zero.mp hdiff').resolve_left hne
  have ha : a = -(r ^ 2 + r * s + s ^ 2) := by
    linear_combination ha'
  refine ⟨ha, ?_⟩
  -- b = -r³ - a r
  have hb0 : b = -r ^ 3 - a * r := by linear_combination hr
  rw [hb0, ha]
  ring
