-- Prove2me | solution 1 for Catalog.Geometry.Peel.peel_extremal_tfae
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:00:43.895777+00:00
-- url     : https://prove2.me/submissions/4a06dbd1-ba1b-4494-a6e7-64bfc689993a

-- Sol generated from Geometry/PeelStoppingTime.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
import Theorems.Thm_Catalog_Geometry_Peel_nsmul_peelRate
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





/-! ## The matching family: equipartition profiles -/


variable {A : ℝ}











open Catalog.Geometry.Peel in
theorem solution(hN : 0 < N) :
    List.TFAE
      [ ∀ k < N, peelGap P k ≤ peelRate P N,
        ∀ k < N, peelGap P k = peelRate P N,
        ∀ k ≤ N, P.size k = P.size 0 - k * peelRate P N,
        ∀ k < N, peelGap P k = peelGap P ((k + 1) % N) ] := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  tfae_have 1 → 2 := by
    intro h k hk
    have hnn : ∀ j ∈ range N, 0 ≤ peelRate P N - peelGap P j := by
      intro j hj
      have := h j (Finset.mem_range.1 hj)
      linarith
    have hsum : ∑ j ∈ range N, (peelRate P N - peelGap P j) = 0 := by
      rw [Finset.sum_sub_distrib, sum_peelGap, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        nsmul_peelRate P]
      ring
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum k (Finset.mem_range.2 hk)
    linarith
  tfae_have 2 → 3 := by
    intro h k hk
    induction k with
    | zero => simp
    | succ n ih =>
        have hn : n < N := by omega
        have hgap := h n hn
        have hprev := ih (by omega)
        simp only [peelGap] at hgap
        push_cast
        linarith
  tfae_have 3 → 1 := by
    intro h k hk
    have h1 := h k (le_of_lt hk)
    have h2 := h (k + 1) hk
    simp only [peelGap]
    push_cast at h2
    linarith
  tfae_have 2 → 4 := by
    intro h k hk
    have hmod : (k + 1) % N < N := Nat.mod_lt _ hN
    rw [h k hk, h _ hmod]
  tfae_have 4 → 2 := by
    intro h
    -- cyclic invariance forces the gap function to be constant on the window
    have hconst : ∀ k, k < N → peelGap P k = peelGap P 0 := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ n ih =>
          intro hn
          have hn' : n < N := by omega
          have hmod : (n + 1) % N = n + 1 := Nat.mod_eq_of_lt hn
          have := h n hn'
          rw [hmod] at this
          rw [← this, ih hn']
    have hsum : ∑ k ∈ range N, peelGap P k = (N : ℝ) * peelGap P 0 := by
      rw [Finset.sum_congr rfl (fun k hk => hconst k (Finset.mem_range.1 hk)),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [sum_peelGap] at hsum
    have h0 : peelGap P 0 = peelRate P N := by
      rw [peelRate, hsum]
      field_simp
    intro k hk
    rw [hconst k hk, h0]
  tfae_finish
