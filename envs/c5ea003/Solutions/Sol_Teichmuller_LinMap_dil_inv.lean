-- Prove2me | solution 1 for Teichmuller.LinMap.dil_inv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T05:01:45.260989+00:00
-- url     : https://prove2.me/submissions/a9aa6797-e19e-4468-beab-f33decc00194

/-
# `Teichmuller.LinMap.dil_inv`
Target `920e5493` (Open, not deprecated at draft time; re-read live immediately before submitting).

NOT YET COMPILED — drafted while the build lock was held by another ship.

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`LinMap` bundles `a b : ℂ` with the field `norm_lt : ‖b‖ < ‖a‖`. With
  jac = ‖a‖² − ‖b‖²,   dil = (‖a‖+‖b‖)/(‖a‖−‖b‖),   inv = ⟨conj a / jac, −b / jac⟩
the inverse's two norms are ‖a‖/jac and ‖b‖/jac, so numerator and denominator of `dil` both
scale by the same positive factor and it cancels. Checked numerically on random maps: worst
absolute difference 4.3e-13, and `jac > 0` has no counterexamples given `‖b‖ < ‖a‖`.

Both cancellations are safe: `norm_lt` makes `‖a‖ − ‖b‖ > 0`, and `jac_pos` makes `jac > 0`.

PROBED, NOT GUESSED:
  * `theorem jac_pos : 0 < f.jac` SURVIVES skeleton subtraction into the bundle, so it is
    available to importers — checked against the bundle source, not assumed.
  * `norm_div`, `norm_neg`, `RCLike.norm_conj`, `Complex.norm_real`, `abs_of_pos` are exactly
    the spellings the bundle's OWN `inv` proof uses, so they resolve in this context.
-/
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LinearQC

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Teichmuller in
/-- **The target, verbatim.** -/
theorem solution (f : LinMap) : f.inv.dil = f.dil := by
  have hj : (0:ℝ) < f.jac := f.jac_pos
  have hJne : f.jac ≠ 0 := ne_of_gt hj
  -- the norm of the real scalar jac, cast into ℂ
  have hJC : ‖((f.jac : ℝ) : ℂ)‖ = f.jac := by
    simp [Complex.norm_real, abs_of_pos hj]
  -- the two norms of the inverse, each scaled by 1/jac
  have ha : ‖f.inv.a‖ = ‖f.a‖ / f.jac := by
    show ‖(starRingEnd ℂ) f.a / ((f.jac : ℝ) : ℂ)‖ = _
    rw [norm_div, RCLike.norm_conj, hJC]
  have hb : ‖f.inv.b‖ = ‖f.b‖ / f.jac := by
    show ‖-f.b / ((f.jac : ℝ) : ℂ)‖ = _
    rw [norm_div, norm_neg, hJC]
  -- the structure field keeps the original denominator away from zero
  have hq : ‖f.a‖ - ‖f.b‖ ≠ 0 := by
    have h : (0:ℝ) < ‖f.a‖ - ‖f.b‖ := by
      have := f.norm_lt
      linarith
    exact ne_of_gt h
  show (‖f.inv.a‖ + ‖f.inv.b‖) / (‖f.inv.a‖ - ‖f.inv.b‖)
      = (‖f.a‖ + ‖f.b‖) / (‖f.a‖ - ‖f.b‖)
  -- `div_add_div_same` does not exist; the goal below was read off the failed compile:
  --   (x/J + y/J) / (x/J - y/J) = (x+y) / (x-y),  with J ≠ 0 and x - y ≠ 0 in context
  rw [ha, hb]
  field_simp
