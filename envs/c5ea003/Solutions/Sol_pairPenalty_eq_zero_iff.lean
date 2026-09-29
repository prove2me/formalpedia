-- Prove2me | solution 1 for pairPenalty_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T10:21:04.895386+00:00
-- url     : https://prove2.me/submissions/b5901d86-d919-4ddc-b688-1af9c5294534

-- Sol generated from Tropical/SATB/TropicalHypergraphCounterpoint.lean
import Mathlib
import Definitions.Def_Tropical_SATB_TropicalHypergraphCounterpoint

/-!
# Tropical Hypergraph Counterpoint for SATB

This module establishes an exact bridge between four-voice (SATB) counterpoint
legality and tropical optimization on weighted hypergraphs.

## Mathematical Content

We model SATB voice leading as a constrained dynamical system on `Fin 4 → ℤ`
and prove three main theorem packages:

### Theorem Package 1: Zero-Locus Characterization
Legal SATB transitions are exactly the zero locus of a nonnegative tropical
penalty functional assembled from six pairwise components (one per unordered
voice pair). This converts Boolean legality into tropical vanishing.

### Theorem Package 2: Shortest-Path Realization
Legal progressions (sequences of chords) are exactly zero-cost paths in the
induced weighted hypergraph. Since all edge weights are nonnegative, legal
paths are globally shortest among all paths with the same endpoints.

### Theorem Package 3: Pairwise Tensor Factorization
The total SATB cost factorizes as a double sum over voice pairs and time steps.
Legality of a full progression is determined entirely by pairwise legality at
each time step, establishing an exact structural decomposition of the 4-voice
problem into coupled 2-voice subproblems.

## Significance

This formalization proves that a high-arity symbolic constraint system (4-voice
counterpoint) admits exact tropical optimization with:
- certifiable legality detection via zero-locus testing,
- shortest-path semantics for legal progressions,
- nontrivial state-space compression via pairwise factorization.
-/

open Finset BigOperators

noncomputable section

/-! ## Core Definitions -/





/-! ## Pairwise Legality Predicates -/









/-! ## Global Legality -/





/-! ## Pairwise Penalty Functions -/






/-! ## Component Penalty Properties -/

theorem parallelFifthPenalty_pair_nonneg (i j : Voice) (v w : Chord) :
    0 ≤ parallelFifthPenalty_pair i j v w := by
  unfold parallelFifthPenalty_pair; split <;> norm_num

theorem crossingPenalty_pair_nonneg (i j : Voice) (w : Chord) :
    0 ≤ crossingPenalty_pair i j w := by
  unfold crossingPenalty_pair; split <;> norm_num

theorem spacingPenalty_pair_nonneg (i j : Voice) (w : Chord) :
    0 ≤ spacingPenalty_pair i j w := by
  unfold spacingPenalty_pair; split <;> norm_num

theorem parallelFifthPenalty_pair_eq_zero_iff (i j : Voice) (v w : Chord) :
    parallelFifthPenalty_pair i j v w = 0 ↔ NoParallelFifthsPair i j v w := by
  unfold parallelFifthPenalty_pair; split <;> simp_all

theorem crossingPenalty_pair_eq_zero_iff (i j : Voice) (w : Chord) :
    crossingPenalty_pair i j w = 0 ↔ NoCrossingPair i j w := by
  unfold crossingPenalty_pair; split <;> simp_all

theorem spacingPenalty_pair_eq_zero_iff (i j : Voice) (w : Chord) :
    spacingPenalty_pair i j w = 0 ↔ SpacingOKPair i j w := by
  unfold spacingPenalty_pair; split <;> simp_all

/-! ## Pairwise Penalty Zero-Locus -/



/-! ## Theorem Package 1: Zero-Locus Characterization -/







/-! ## Theorem Package 2: Shortest-Path Realization -/






/-! ## Theorem Package 3: Pairwise Tensor Factorization -/




/-! ## Additional Results: Tropical Structure -/







theorem solution(i j : Voice) (v w : Chord) :
    pairPenalty i j v w = 0 ↔ PairLegal i j v w := by
  simp only [pairPenalty, PairLegal]
  constructor
  · intro h
    have h1 : parallelFifthPenalty_pair i j v w ≤ 0 := by
      linarith [le_max_left (parallelFifthPenalty_pair i j v w)
        (max (crossingPenalty_pair i j w) (spacingPenalty_pair i j w))]
    have h2 : crossingPenalty_pair i j w ≤ 0 := by
      linarith [le_max_right (parallelFifthPenalty_pair i j v w)
        (max (crossingPenalty_pair i j w) (spacingPenalty_pair i j w)),
        le_max_left (crossingPenalty_pair i j w) (spacingPenalty_pair i j w)]
    have h3 : spacingPenalty_pair i j w ≤ 0 := by
      linarith [le_max_right (parallelFifthPenalty_pair i j v w)
        (max (crossingPenalty_pair i j w) (spacingPenalty_pair i j w)),
        le_max_right (crossingPenalty_pair i j w) (spacingPenalty_pair i j w)]
    exact ⟨(parallelFifthPenalty_pair_eq_zero_iff i j v w).mp
             (le_antisymm h1 (parallelFifthPenalty_pair_nonneg i j v w)),
           (crossingPenalty_pair_eq_zero_iff i j w).mp
             (le_antisymm h2 (crossingPenalty_pair_nonneg i j w)),
           (spacingPenalty_pair_eq_zero_iff i j w).mp
             (le_antisymm h3 (spacingPenalty_pair_nonneg i j w))⟩
  · intro ⟨h1, h2, h3⟩
    rw [← parallelFifthPenalty_pair_eq_zero_iff] at h1
    rw [← crossingPenalty_pair_eq_zero_iff] at h2
    rw [← spacingPenalty_pair_eq_zero_iff] at h3
    simp [h1, h2, h3]
