-- Prove2me | solution 1 for Catalog.Geometry.Peel.peelEstimate_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:30:16.72376+00:00
-- url     : https://prove2.me/submissions/de081ad5-432f-4a74-accf-9ac67754a90e

-- Sol generated from Geometry/PeelStoppingTime.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
import Theorems.Thm_Catalog_Geometry_Peel_nsmul_peelRate
import Theorems.Thm_Catalog_Geometry_Peel_peelRate_nonneg
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











open Catalog.Geometry.Peel in
theorem solution(hk : k ≤ N) :
    |P.size k - peelEstimate P N k| ≤ peelBudget P N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    simp [peelEstimate, peelBudget]
  have hrate := peelRate_nonneg P N
  have hsizes : P.size N ≤ P.size k ∧ P.size k ≤ P.size 0 :=
    ⟨P.anti hk, P.anti (Nat.zero_le k)⟩
  have hest : P.size N ≤ peelEstimate P N k ∧ peelEstimate P N k ≤ P.size 0 := by
    constructor
    · have hkN : (k : ℝ) * peelRate P N ≤ (N : ℝ) * peelRate P N := by
        have : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
        nlinarith
      rw [nsmul_peelRate P] at hkN
      simp only [peelEstimate, peelBudget] at *
      linarith
    · have : 0 ≤ (k : ℝ) * peelRate P N := mul_nonneg (Nat.cast_nonneg k) hrate
      simp only [peelEstimate]
      linarith
  rw [abs_le]
  simp only [peelBudget]
  constructor <;> [linarith [hsizes.1, hest.2]; linarith [hsizes.2, hest.1]]
