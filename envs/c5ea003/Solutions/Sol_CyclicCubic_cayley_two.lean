-- Prove2me | solution 1 for CyclicCubic.cayley_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:14:03.505341+00:00
-- url     : https://prove2.me/submissions/0395e5e7-983e-4fef-b303-71bd4f34a0c3

/-
# `CyclicCubic.cayley_two`
Target `07a06d55` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle built. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries SEVEN):
    ∀ {R : Type} [CommRing R] [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R),
      M ^ 2 = M.trace • M - M.det • 1
`[Nontrivial R]` IS required here — unlike its section-mate `companion_sq`, whose WA shows only
`[CommRing R]`. The difference is real: this statement recovers `trace` and `det` from an ARBITRARY
matrix, where `companion_sq`'s matrix is given explicitly. Adjacent theorems in one section needing
different instances is the recurring trap in these bundles.

MATHS — Cayley–Hamilton in dimension two, done by hand. For `M = !![a, b; c, d]`:
    trace M = a + d,  det M = a·d − b·c
    M²      = !![a² + b·c,  a·b + b·d;  c·a + d·c,  c·b + d²]
    (a+d)•M − (a·d − b·c)•1
            = !![a² + a·d − a·d + b·c,  a·b + b·d;  c·a + c·d,  a·d + d² − a·d + b·c]
            = !![a² + b·c,  a·b + b·d;  c·a + c·d,  b·c + d²]
Equal entrywise. So the proof is `Matrix.ext`, a `Fin 2` case split on both indices, expansion of
`trace`/`det`/`mul` on `Fin 2`, and `ring` on each of the four scalar goals.

`decide` is unavailable — `R` is an arbitrary commutative ring, not a finite type — so each entry has
to be closed by ring normalisation. `Matrix.det_fin_two` and `Matrix.trace_fin_two` are the lemmas
that put the two scalars into explicit form.
-/
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting

set_option autoImplicit false
set_option maxHeartbeats 400000

open CyclicCubic Matrix

open CyclicCubic in
/-- **The target, verbatim.** -/
theorem solution {R : Type*} [CommRing R] [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • 1 := by
  rw [pow_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring
