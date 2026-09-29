-- Prove2me | solution 1 for ToricCode.d1T_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:50:33.60479+00:00
-- url     : https://prove2.me/submissions/26c9068a-e8db-49a7-8d56-f80e025c41e9

-- Sol generated from Geometry/ToricCode/Basic.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic

/-!
# The `M × N` torus surface code: cellular chain complex

This file builds the *geometric* object requested by target 3 of the previous
research cycle: the cellular chain complex of the standard square-grid
cellulation of the two-dimensional torus `(ℤ/M) × (ℤ/N)`, over the binary field
`𝔽₂`.

* vertices  `Vert M N = ZMod M × ZMod N`                      (`MN` of them),
* edges     `Edge M N = Bool × ZMod M × ZMod N`               (`2MN` of them):
  the edge `(false, u)` joins `u` to `u + (1,0)`, the edge `(true, u)` joins `u`
  to `u + (0,1)`,
* faces     `Face M N = ZMod M × ZMod N`                      (`MN` of them):
  the face `f` is the unit square with corners `f, f+(1,0), f+(0,1), f+(1,1)`.

The two boundary matrices are `d1 : Vert × Edge` and `d2 : Edge × Face`.  The
main content of this file is a set of *explicit pointwise formulas* for the four
maps `d1 *ᵥ ·`, `d2 *ᵥ ·`, `d1ᵀ *ᵥ ·`, `d2ᵀ *ᵥ ·`, together with the chain
condition `d1 ∘ d2 = 0`.  Everything downstream is proved from these formulas,
never by unfolding the matrices again.
-/

open Matrix

open ToricCode


variable (M N : ℕ) [NeZero M] [NeZero N]








/-! ### Pointwise formulas -/


private lemma sum_two_ind_comm (s v : ZMod M × ZMod N) (f : (ZMod M × ZMod N) → F2) :
    ∑ u : ZMod M × ZMod N,
        ((if u = v then (1:F2) else 0) + (if u = v + s then 1 else 0)) * f u
      = f v + f (v + s) := by
  classical
  have h : ∀ u : ZMod M × ZMod N,
      ((if u = v then (1:F2) else 0) + (if u = v + s then 1 else 0)) * f u
        = (if v = u then f u else 0) + (if v + s = u then f u else 0) := by
    intro u
    simp only [add_mul, ite_mul, one_mul, zero_mul]
    congr 2 <;> simp only [eq_iff_iff] <;> exact eq_comm
  rw [Finset.sum_congr rfl (fun u _ => h u), Finset.sum_add_distrib]
  simp





/-! ### The chain condition -/




/-! ### Basic counting -/




/-! ### Kernels of the two coboundary operators are the constants -/



open ToricCode in
theorem solution(h : Vert M N → F2) (b : Bool) (u : ZMod M × ZMod N) :
    ((d1 M N)ᵀ *ᵥ h) (b, u) = h u + h (u + step M N b) := by
  classical
  simp only [Matrix.mulVec, Matrix.transpose_apply, d1, dotProduct]
  exact sum_two_ind_comm M N (step M N b) u h
