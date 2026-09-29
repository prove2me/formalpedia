-- Prove2me | Theorems.Thm_heightSignature_submaximal_of_finiteHeight
-- name    : heightSignature_submaximal_of_finiteHeight
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:33:32.246223+00:00
-- url     : https://prove2.me/theorems/d1a7e421-f0ee-4eaf-9ac2-3a429e2a36b1
-- title:
--   Finite-height witnesses force submaximal signatures at small scales.
-- statement:
--   **Finite-height witnesses force submaximal signatures at small scales.**
--
--   ```lean
--   theorem heightSignature_submaximal_of_finiteHeight    (P : PrimeSlopeProfile)
--       (hw : HasFiniteHeightWitness P) :
--       ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → ε < ε₀ →
--         heightSignature P ε < P.slopes.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/ArithmeticPersistence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/ArithmeticPersistence.lean#L126

-- Thm stub generated from Bridges/NeuralCoding/ArithmeticPersistence.lean
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

theorem heightSignature_submaximal_of_finiteHeight    (P : PrimeSlopeProfile)
    (hw : HasFiniteHeightWitness P) :
    ∃ ε₀ : ℚ, 0 < ε₀ ∧ ∀ ε : ℚ, 0 < ε → ε < ε₀ →
      heightSignature P ε < P.slopes.card := by sorry
