-- Prove2me | solution 1 for CyclicCubic.companion_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:10:12.026061+00:00
-- url     : https://prove2.me/submissions/b805c475-17b1-4fce-9010-46d90b5d9b67

/-
# `CyclicCubic.companion_sq`
Target `d15566dc` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle built. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries SEVEN):
    ∀ {R : Type} [CommRing R] (x : R), !![x, -1; 1, 0] ^ 2 = x • !![x, -1; 1, 0] - 1
`R` implicit from `section Matrices`' `variable {R : Type*} [CommRing R]` (line 69); `x` explicit.
NO `[Nontrivial R]` — unlike the sibling `cayley_two`, which does carry it. Adjacent theorems in the
same section genuinely differ, so the list is taken from THIS target's rejection.

MATHS. The companion matrix of `t² - x t + 1`. Squaring it is a direct 2×2 computation:
    !![x,-1; 1,0]² = !![x·x + (-1)·1, x·(-1) + (-1)·0; 1·x + 0·1, 1·(-1) + 0·0]
                   = !![x² - 1, -x; x, -1]
and the right-hand side is
    x • !![x,-1; 1,0] - 1 = !![x² , -x; x, 0] - !![1,0; 0,1] = !![x² - 1, -x; x, -1].
Equal entrywise. So the proof is `Matrix.ext` followed by a `Fin 2` case split and `ring` on each of
the four entries — `decide` cannot help because `R` is an arbitrary commutative ring.

The idiom for this in Mathlib is to normalise with the `!![ ]` simp set (`Matrix.mul_fin_two`,
`Matrix.smul_of`, `Matrix.one_fin_two`, `Matrix.sub_of`) and finish with `ring`, rather than to
unfold `Matrix.mul` by hand.
-/
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting

set_option autoImplicit false
set_option maxHeartbeats 400000

open CyclicCubic Matrix

open CyclicCubic in
/-- **The target, verbatim.** -/
theorem solution {R : Type*} [CommRing R] (x : R) :
    (!![x, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ 2 = x • !![x, -1; 1, 0] - 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring
