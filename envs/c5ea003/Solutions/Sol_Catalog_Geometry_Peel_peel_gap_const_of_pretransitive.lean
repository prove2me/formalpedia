-- Prove2me | solution 1 for Catalog.Geometry.Peel.peel_gap_const_of_pretransitive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:30:17.360712+00:00
-- url     : https://prove2.me/submissions/41c6cfb1-dbcc-4e49-937b-b47e49cab448

-- Sol generated from Geometry/PeelStoppingTime.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
import Theorems.Thm_Catalog_Geometry_Peel_sum_peelGap
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


lemma sum_gapFin (N : ℕ) : ∑ i : Fin N, gapFin P N i = peelBudget P N := by
  have h := Fin.sum_univ_eq_sum_range (fun k => peelGap P k) N
  simp only [gapFin]
  rw [h, sum_peelGap]



/-! ## The matching family: equipartition profiles -/


variable {A : ℝ}











open Catalog.Geometry.Peel in
theorem solution(hN : 0 < N) {G : Type*} [Group G]
    [MulAction G (Fin N)] [MulAction.IsPretransitive G (Fin N)]
    (hinv : ∀ (g : G) (i : Fin N), gapFin P N (g • i) = gapFin P N i) :
    ∀ i : Fin N, gapFin P N i = peelRate P N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  haveI : NeZero N := ⟨hN.ne'⟩
  have hconst : ∀ i : Fin N, gapFin P N i = gapFin P N 0 := by
    intro i
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (0 : Fin N) i
    rw [← hg, hinv]
  have hsum : (N : ℝ) * gapFin P N 0 = peelBudget P N := by
    rw [← sum_gapFin P N, Finset.sum_congr rfl (fun i _ => hconst i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  intro i
  rw [hconst i, peelRate, ← hsum]
  field_simp
