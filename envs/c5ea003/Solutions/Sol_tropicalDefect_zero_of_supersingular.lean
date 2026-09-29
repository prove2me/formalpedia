-- Prove2me | solution 1 for tropicalDefect_zero_of_supersingular
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:27:12.353991+00:00
-- url     : https://prove2.me/submissions/bd3fd3d8-568d-4918-b2e0-89837786ca0a

-- Sol generated from Bridges/NeuralCoding/ArithmeticPersistence.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_ArithmeticPersistence

/-!
# Arithmetic Persistence for K3 Height Detection

This file develops the theory of **primewise arithmetic persistence**, a framework
connecting persistent homology statistics to the height dichotomy (ordinary vs.
supersingular) of formal Brauer groups in K3 surface reductions.

## Main definitions

* `PrimeSlopeProfile` — A finite set of rational "slopes" representing
  normalized Frobenius eigenvalue data at a prime, together with a symmetry center.
* `heightSignature` — A computable statistic measuring concentration of slopes
  near the symmetry center at scale ε.
* `persistentRank` — The filtration-indexed version of the height signature.
* `IsSupersingularProfile` — Predicate: all slopes equal the symmetry center.
* `HasFiniteHeightWitness` — Predicate: some slope differs from the center.
* `tropicalDefect` — A max-plus statistic detecting supersingularity.
* `classifyHeightRegime` — A certified Boolean classifier for the height dichotomy.

## Main results

* `heightSignature_maximal_iff_supersingular` — Exact separation: height signature
  is maximal at all scales iff the profile is supersingular.
* `heightSignature_submaximal_of_finiteHeight` — Finite-height witnesses produce
  submaximal signatures at small scales.
* `persistentRank_monotone` — The persistent rank function is monotone.
* `firstJump_characterization` — Finite-height profiles have a computable first jump.
* `tropicalDefect_zero_iff_supersingular` — Tropical defect vanishes iff supersingular.
* `classifyHeightRegime_correct_supersingular` — Classifier correctness (supersingular).
* `classifyHeightRegime_correct_gap` — Classifier correctness (finite height).

## Mathematical context

For a K3 surface X over a number field, reduction mod a good prime p yields
a formal Brauer group of height h ∈ {1,…,10,∞}. Height ∞ corresponds to
supersingular reduction where all crystalline Frobenius slopes in weight 2
equal the symmetry center (slope 1). Finite height forces slopes away from 1.

This file abstracts the detection mechanism: slope concentration at the center
is equivalent to supersingularity, and this can be read off by persistence-style
filtration statistics. The abstraction is rigorous and the theorems are fully proved.
-/

open Finset

/-! ## Core structures -/


/-! ## Height dichotomy predicates -/






/-! ## Height signature and persistent rank -/




/-! ## Theorem 1: Exact separation by concentration statistic -/




/-! ## Persistent rank monotonicity and jump detection -/






/-! ## Tropical defect (max-based) -/






/-! ## Certified classifier -/




/-! ## Persistence filtration model -/




/-! ## Conjectural K3 geometric realization -/


theorem solution    (P : PrimeSlopeProfile)
    (hss : IsSupersingularProfile P)
    (t : ℚ) (ht : 0 ≤ t) :
    tropicalDefect P t = 0 := by
  unfold tropicalDefect
  split
  case isTrue h =>
    apply le_antisymm
    · apply sup'_le
      intro s hs
      rw [hss s hs, sub_self, abs_zero, zero_sub]
      exact max_le (le_refl 0) (neg_nonpos_of_nonneg ht)
    · obtain ⟨s₀, hs₀⟩ := h
      exact le_trans (le_max_left 0 _)
        (le_sup' (fun s => max 0 (|s - P.symmetric_about| - t)) hs₀)
  case isFalse => rfl
