-- Prove2me | solution 1 for Goldbach.density_kernel_laplace_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T03:42:07.304275+00:00
-- url     : https://prove2.me/submissions/d1e8bd69-b1af-435c-995d-dbf1fff7fbe5

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open MeasureTheory
set_option autoImplicit false

theorem solution (z : ℝ) (hz : z ≠ 0) :
    (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-z*u)) =
      (16*z^5-40*z^3+60*z^2-60+60*Real.exp (-2*z)*(z+1)^2)/(15*z^6) := by
  let a0 : ℝ := -16/(15*z)+8/(3*z^3)-4/z^4+4/z^6
  let a1 : ℝ := 8/(3*z^2)-4/z^3+4/z^5
  let a2 : ℝ := 4/(3*z)-2/z^2+2/z^4
  let a3 : ℝ := -2/(3*z)+2/(3*z^3)
  let a4 : ℝ := 1/(6*z^2)
  let a5 : ℝ := 1/(30*z)
  let Q : ℝ → ℝ := fun u => a0+a1*u+a2*u^2+a3*u^3+a4*u^4+a5*u^5
  have hQ (u : ℝ) : HasDerivAt Q (a1+2*a2*u+3*a3*u^2+4*a4*u^3+5*a5*u^4) u := by
    convert (((((hasDerivAt_const u a0).add ((hasDerivAt_id u).const_mul a1)).add
      ((hasDerivAt_pow 2 u).const_mul a2)).add ((hasDerivAt_pow 3 u).const_mul a3)).add
      ((hasDerivAt_pow 4 u).const_mul a4)).add ((hasDerivAt_pow 5 u).const_mul a5) using 1
    dsimp [Q]
    ring
  have hd (u : ℝ) : HasDerivAt (fun v => Q v*Real.exp (-z*v))
      (((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-z*u)) u := by
    have he := (Real.hasDerivAt_exp (-z*u)).comp u ((hasDerivAt_id u).const_mul (-z))
    convert (hQ u).mul he using 1
    dsimp [Q,a0,a1,a2,a3,a4,a5]
    field_simp
    ring
  have hint : IntervalIntegrable
      (fun u : ℝ => ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-z*u)) volume 0 2 :=
    (by fun_prop : Continuous
      (fun u : ℝ => ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-z*u))).intervalIntegrable 0 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u) hint]
  dsimp [Q,a0,a1,a2,a3,a4,a5]
  have he : -z*2 = -2*z := by ring
  rw [he]
  norm_num
  field_simp
  ring

#print axioms solution
