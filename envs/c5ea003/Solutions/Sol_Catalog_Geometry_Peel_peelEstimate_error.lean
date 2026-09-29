-- Prove2me | solution 1 for Catalog.Geometry.Peel.peelEstimate_error
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:30:15.946125+00:00
-- url     : https://prove2.me/submissions/c8068d9b-48b4-4038-a85f-f319865ba630

-- Sol generated from Geometry/PeelStoppingTime.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
import Theorems.Thm_Catalog_Geometry_Peel_peelEstimate_error_eq
import Theorems.Thm_Catalog_Geometry_Peel_peelEstimate_error_tail_eq
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




lemma peelGap_nonneg (k : ℕ) : 0 ≤ peelGap P k :=
  sub_nonneg.2 (P.anti (Nat.le_succ k))





/-! ## The upper bound: existence of a good stopping time -/










/-! ## Density of good stopping times -/



/-! ## Stable windows: blocks of consecutive small layers -/



/-! ## Rigidity: the pigeonhole bound is saturated only by arithmetic profiles -/


/-! ## Symmetry forces extremality -/





/-! ## The matching family: equipartition profiles -/


variable {A : ℝ}











open Catalog.Geometry.Peel in
theorem solution(hk : k ≤ N) :
    |P.size k - peelEstimate P N k| ≤ (max k (N - k) : ℕ) * peelRate P N := by
  have hrate := peelRate_nonneg P N
  have hupper : P.size k - peelEstimate P N k ≤ (k : ℝ) * peelRate P N := by
    rw [peelEstimate_error_eq]
    calc ∑ j ∈ range k, (peelRate P N - peelGap P j)
        ≤ ∑ _j ∈ range k, peelRate P N := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := peelGap_nonneg P j; linarith
      _ = (k : ℝ) * peelRate P N := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htail := peelEstimate_error_tail_eq P hk
  have hlower : -((N - k : ℕ) : ℝ) * peelRate P N ≤ P.size k - peelEstimate P N k := by
    have hle : ∑ j ∈ Finset.Ico k N, (peelRate P N - peelGap P j)
        ≤ ((N - k : ℕ) : ℝ) * peelRate P N := by
      calc ∑ j ∈ Finset.Ico k N, (peelRate P N - peelGap P j)
          ≤ ∑ _j ∈ Finset.Ico k N, peelRate P N := by
            refine Finset.sum_le_sum fun j _ => ?_
            have := peelGap_nonneg P j; linarith
        _ = ((N - k : ℕ) : ℝ) * peelRate P N := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [htail] at hle
    linarith
  have h1 : (k : ℝ) ≤ ((max k (N - k) : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_left _ _
  have h2 : ((N - k : ℕ) : ℝ) ≤ ((max k (N - k) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_right _ _
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith
