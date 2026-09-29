-- Prove2me | solution 1 for Knot.Khovanov.enhancement_state_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:14.410903+00:00
-- url     : https://prove2.me/submissions/b97bb71c-0518-455f-8711-f408a17eef7d

-- Sol generated from Geometry/KnotTheory/KhovanovCategorification.lean
import Mathlib
import Definitions.Def_Geometry_KnotTheory_Defs
import Definitions.Def_Geometry_KnotTheory_KhovanovCategorification
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/

/-!
# The graded Euler state sum underlying Khovanov homology

This file formalizes the decategorification calculation for an arbitrary link
diagram.  A Khovanov generator consists of a smoothing state together with a
choice of one of the two quantum basis vectors on every resulting circle.  The
main theorem proves that the graded Euler sum of these generators is the
corresponding Jones state sum.
-/

open Knot.Khovanov

open Finset LaurentPolynomial








/-- The enhancement degree splits into the degree of the first circle and the
degree of the remaining circles. -/
theorem enhancementDegree_cons {m : ℕ} (b : Bool) (e : Fin m → Bool) :
    enhancementDegree (Fin.cons b e) =
      (if b then 1 else -1) + enhancementDegree e := by
  simp [enhancementDegree, Fin.sum_univ_succ]








open Knot.Khovanov in
theorem solution(m : ℕ) :
    ∑ e : Fin m → Bool, T (enhancementDegree e) =
      (T 1 + T (-1) : LaurentPolynomial ℤ) ^ m := by
  induction m with
  | zero => simp [enhancementDegree]
  | succ m ih =>
      rw [Fintype.sum_equiv (enhancementSuccEquiv m)
        (fun e => T (enhancementDegree e))
        (fun p => T ((if p.1 then 1 else -1) + enhancementDegree p.2))]
      · rw [Fintype.sum_prod_type]
        simp only [T_add, Fintype.sum_bool, if_true,
          Bool.false_eq_true, if_false]
        rw [← Finset.mul_sum, ← Finset.mul_sum, ih, pow_succ']
        ring
      · intro e
        rw [← enhancementDegree_cons]
        exact congrArg (fun x => T (enhancementDegree x))
          ((enhancementSuccEquiv m).left_inv e).symm
