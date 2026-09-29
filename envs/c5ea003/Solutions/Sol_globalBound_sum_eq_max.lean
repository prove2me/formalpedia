-- Prove2me | solution 1 for globalBound_sum_eq_max
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:09:36.324762+00:00
-- url     : https://prove2.me/submissions/8d20a3fd-10a5-44f9-8dee-1fef140e2a09

-- Sol generated from Bridges/PosetTheory/ExceptionalExpanderLadder.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_ExceptionalExpanderLadder
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exceptional Expander Ladder: F₄, E₆, E₇, E₈

This file builds the exceptional analogue of the certified G₂ expander framework
from `Pythagorean.G2CharacterSheafCertificate`. It introduces a certificate theory
for exceptional groups, proving nontrivial structural theorems about finite
optimization over torus types, certificate refinement monotonicity, and spectral
safety margins.

## Architecture

The key conceptual advance is **torus-type reduction**: instead of verifying
character-ratio bounds over all group elements, we reduce to a finite optimization
over Weyl-conjugacy classes of maximal tori. This turns an infinite
representation-theoretic assertion into a finite certified maximization.

## Main Results

1. `le_globalBound`: Every local bound is dominated by the global bound.
2. `exists_torusType_attaining_globalBound`: The global bound is attained.
3. `globalBound_mono_under_refinement`: Certificate refinement cannot worsen bounds.
4. `refinement_increases_spectralSafetyMargin`: Refinement improves spectral margin.
5. `globalBound_nonneg`: Nonnegativity propagation from local to global.
6. `globalBound_of_rational_localBound`: Rational local bounds yield rational global.
7. `exceptional_to_CharRatioCert`: Bridge to G₂ certificate framework.
8. `exceptional_uniform_expansion_clean`: Exceptional certificates yield uniform
   expansion for large q.
9. `globalBound_sum_eq_max`: The global bound of a sum is the max of the parts.
10. `globalBound_mono_trans`: Transitivity of refinement monotonicity.

## Cross-Domain Connections

- **Exceptional Lie theory → spectral graph theory**: `positive_spectralSafetyMargin_of_certified_gap`
- **Exceptional Lie theory → combinatorial optimization**: `argmaxTorusType_spec`
- **Exceptional Lie theory → G₂ certificate framework**: `exceptional_to_CharRatioCert`

## References

* Deligne–Lusztig (1976), Carter (1985), Liebeck–Shalev (2004),
  Gowers (2008), Lubotzky (2012).
-/


open Finset Filter

/-! ## §1. Exceptional Family Structure -/


attribute [instance] ExceptionalFamily.torusTypeFintype
attribute [instance] ExceptionalFamily.torusTypeNonempty

/-! ## §2. Global Bound via Finite Maximum -/




/-- The global bound is at most any upper bound on all local bounds. -/
theorem globalBound_le_of_forall_le (F : ExceptionalFamily) (M : ℝ)
    (hM : ∀ t, F.localBound t ≤ M) :
    globalBound F ≤ M := by
  obtain ⟨t, ht⟩ := exists_torusType_attaining_globalBound F
  rw [ht]; exact hM t

/-! ## §3. Exceptional Certificate Structure -/



/-! ## §4. Toral Reduction Theorems -/



/-! ## §5. Certificate Refinement -/



/-! ## §6. Toral Complexity Profile -/




/-! ## §7. Spectral Safety Margin -/




/-! ## §8. Nonnegativity Propagation -/



/-! ## §9. Rational Local Bounds and Global Bound -/


/-! ## §10. Certified Finite Search Algorithm -/



/-! ## §11. Bridge to CharacterRatioCertificate -/






/-! ## §12. Exceptional Uniform Expansion -/


/-! ## §13. Global Bound Algebra -/


/-! ## §14. Exceptional Type Enumeration -/









/-! ## §15. Conjectural Exceptional Toral Boundedness -/



/-! ## §16. Compositional Certificate Theory -/


/-- The global bound of a sum dominates the left component. -/
theorem globalBound_sum_ge_left (F₁ F₂ : ExceptionalFamily) :
    globalBound F₁ ≤ globalBound (F₁.sum F₂) := by
  obtain ⟨t, ht⟩ := exists_torusType_attaining_globalBound F₁
  rw [ht]; exact le_globalBound (F₁.sum F₂) (Sum.inl t)

/-- The global bound of a sum dominates the right component. -/
theorem globalBound_sum_ge_right (F₁ F₂ : ExceptionalFamily) :
    globalBound F₂ ≤ globalBound (F₁.sum F₂) := by
  obtain ⟨t, ht⟩ := exists_torusType_attaining_globalBound F₂
  rw [ht]; exact le_globalBound (F₁.sum F₂) (Sum.inr t)


/-! ## §17. Transitivity of Refinement -/



/-! ## §18. Spectral Safety Margin Algebra -/





theorem solution(F₁ F₂ : ExceptionalFamily) :
    globalBound (F₁.sum F₂) = max (globalBound F₁) (globalBound F₂) := by
  apply le_antisymm
  · apply globalBound_le_of_forall_le
    intro t
    cases t with
    | inl t₁ =>
      simp only [ExceptionalFamily.sum, Sum.elim_inl]
      exact (le_globalBound F₁ t₁).trans (le_max_left _ _)
    | inr t₂ =>
      simp only [ExceptionalFamily.sum, Sum.elim_inr]
      exact (le_globalBound F₂ t₂).trans (le_max_right _ _)
  · exact max_le (globalBound_sum_ge_left F₁ F₂) (globalBound_sum_ge_right F₁ F₂)
