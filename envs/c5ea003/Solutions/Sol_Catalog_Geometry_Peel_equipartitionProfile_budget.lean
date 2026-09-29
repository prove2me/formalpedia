-- Prove2me | solution 1 for Catalog.Geometry.Peel.equipartitionProfile_budget
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:21:59.746856+00:00
-- url     : https://prove2.me/submissions/da39c3de-b7be-4865-b7f3-586272488609

-- Sol generated from Geometry/PeelStoppingTime.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
import Theorems.Thm_Catalog_Geometry_Peel_equipartitionProfile_size_of_le
/-
# Peeling profiles, stopping times, and the rigidity of the pigeonhole bound

A *peeling process* is the abstract skeleton shared by a large family of
geometric arguments: one removes successive "layers" from a body and records
the remaining content.  Formally the data is a nonincreasing, nonnegative
sequence `size : ℕ → ℝ` (`PeelProfile`), whose successive differences
`peelGap` are the layer contents.

The classical *upper bound* half of the theory is a pigeonhole statement:
inside any window of `N` peeling steps there is a step whose layer content is
at most the average `peelRate = (size 0 - size N)/N`.  This file formalises
that half (`exists_peel_stopping_time`, `peelEstimate_error`,
`peel_gap_density`, `exists_peel_stable_window`) and then goes further, to the
question of *sharpness*:

* `peel_extremal_tfae` — a four-way equivalence showing that the pigeonhole
  bound is saturated exactly by the arithmetic (equipartition) profiles, and
  that saturation is equivalent to invariance of the gap function under the
  cyclic shift of `ZMod N`.  This is the rigidity statement that converts the
  inequality into a classification.
* `peel_gap_const_of_pretransitive` — the group-theoretic form: if *any* group
  acts pretransitively on the `N` peeling steps and the gap function is
  invariant, all gaps equal the average.  Symmetry forces extremality.

`Catalog/Geometry/PeelSymmetryConstruction.lean` supplies the matching
geometric family of actions (equal-volume shell peelings of Euclidean balls,
equivariant for the orthogonal group).

## Lab notes

Numerical sanity checks performed while developing the file (see
`ComputationalEvidence.md`): the extremal profile for `N = 4`, `A = 1` is
`1, 3/4, 1/2, 1/4, 0`, all gaps `1/4`; the "front-loaded" profile
`1, 0, 0, 0, 0` has gaps `1, 0, 0, 0`, minimum gap `0 < 1/4`, illustrating
that the pigeonhole bound is far from an equality in general and that the
rigidity statement really needs the *uniform* smallness hypothesis.
-/

open Catalog.Geometry.Peel

open Finset

/-! ## Peeling profiles -/


variable (P : PeelProfile) {N J M k : ℕ}









/-! ## The upper bound: existence of a good stopping time -/










/-! ## Density of good stopping times -/



/-! ## Stable windows: blocks of consecutive small layers -/



/-! ## Rigidity: the pigeonhole bound is saturated only by arithmetic profiles -/


/-! ## Symmetry forces extremality -/





/-! ## The matching family: equipartition profiles -/


variable {A : ℝ}


@[simp] lemma equipartitionProfile_zero (hA : 0 ≤ A) (hN : 0 < N) :
    (equipartitionProfile A hA N).size 0 = A := by
  rw [equipartitionProfile_size_of_le hA hN (Nat.zero_le N)]; simp

@[simp] lemma equipartitionProfile_last (hA : 0 ≤ A) (hN : 0 < N) :
    (equipartitionProfile A hA N).size N = 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [equipartitionProfile_size_of_le hA hN (le_refl N), div_self hNR.ne']
  ring








open Catalog.Geometry.Peel in
theorem solution(hA : 0 ≤ A) (hN : 0 < N) :
    peelBudget (equipartitionProfile A hA N) N = A := by
  simp [peelBudget, hN]
