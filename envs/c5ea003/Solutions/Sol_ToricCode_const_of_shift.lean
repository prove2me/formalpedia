-- Prove2me | solution 1 for ToricCode.const_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:41:54.496212+00:00
-- url     : https://prove2.me/submissions/75fc0a50-030e-405d-917d-28aab739270e

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







/-! ### The chain condition -/




/-! ### Basic counting -/




/-! ### Kernels of the two coboundary operators are the constants -/



open ToricCode in
theorem solution(f : ZMod M × ZMod N → F2)
    (hx : ∀ u : ZMod M × ZMod N, f (u + (1, 0)) = f u)
    (hy : ∀ u : ZMod M × ZMod N, f (u + (0, 1)) = f u) :
    ∀ u, f u = f 0 := by
  have hz : ((0 : ZMod M), (0 : ZMod N)) = 0 := rfl
  have hxn : ∀ (n : ℕ) (u : ZMod M × ZMod N), f (u + ((n : ZMod M), 0)) = f u := by
    intro n
    induction n with
    | zero => intro u; rw [Nat.cast_zero, hz, add_zero]
    | succ k ih =>
        intro u
        obtain ⟨a, b⟩ := u
        have h : ((a, b) : ZMod M × ZMod N) + (((k + 1 : ℕ) : ZMod M), 0)
            = ((a, b) + ((k : ZMod M), 0)) + (1, 0) := by
          push_cast
          simp only [Prod.mk_add_mk, Prod.mk.injEq]
          constructor <;> ring
        rw [h, hx, ih]
  have hyn : ∀ (n : ℕ) (u : ZMod M × ZMod N), f (u + (0, (n : ZMod N))) = f u := by
    intro n
    induction n with
    | zero => intro u; rw [Nat.cast_zero, hz, add_zero]
    | succ k ih =>
        intro u
        obtain ⟨a, b⟩ := u
        have h : ((a, b) : ZMod M × ZMod N) + (0, ((k + 1 : ℕ) : ZMod N))
            = ((a, b) + (0, (k : ZMod N))) + (0, 1) := by
          push_cast
          simp only [Prod.mk_add_mk, Prod.mk.injEq]
          constructor <;> ring
        rw [h, hy, ih]
  intro u
  obtain ⟨x, y⟩ := u
  have e1 : f (x, 0) = f 0 := by
    have h := hxn x.val 0
    rw [ZMod.natCast_rightInverse x] at h
    rw [← h, zero_add]
  have e2 : f (x, y) = f (x, 0) := by
    have h := hyn y.val (x, 0)
    rw [ZMod.natCast_rightInverse y] at h
    rw [← h]
    congr 1
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  rw [e2, e1]
