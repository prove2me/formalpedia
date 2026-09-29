-- Prove2me | solution 1 for TropicalGeometricLanglandsMV.admissible_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T11:14:20.283863+00:00
-- url     : https://prove2.me/submissions/644b806f-e357-4365-bb6b-3f01b5f90a55

-- Sol generated from Bridges/TropicalGeometricLanglandsMV.lean
import Mathlib
import Definitions.Def_Bridges_TropicalGeometricLanglandsMV

/-!
# Tropical Geometric Langlands via Idempotent Affine Grassmannian Semirings
# and Certified Mirković–Vilonen Polytope Reconstruction

## Overview

We formalize a bridge between idempotent (tropical/min-plus) convolution algebra
and representation-theoretic geometry, proving:

1. **Classification**: Admissible characters over a tropical Hecke chamber complex
   are in canonical bijection with tropical MV-type polytopes.
2. **Monoidality**: Convolution of characters corresponds to Minkowski addition.
3. **Certified Reconstruction**: Extremal character values uniquely determine the
   associated tropical MV polytope.
4. **Concrete semimodules**: Min-plus action on a finite state space yields
   admissible characters.

## Mathematical Significance

This upgrades tropical Satake from a coarse correspondence to a geometric
representation classifier. In the idempotent world, MV geometry is recovered
from the convex envelope of spectral extremals.
-/

open Finset Function

noncomputable section

open TropicalGeometricLanglandsMV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1. Chamber Complex -/


attribute [instance] ChamberComplex.adj_dec

/-! ## §2. Tropical MV Polytopes

A tropical MV polytope of level `k` has weight differences bounded by
`k * edgeWeight(i,j)`. The level corresponds to the highest weight
in classical representation theory. -/




/-
Edge bound in both directions.
-/

/-! ## §3. Admissible Characters -/



/-! ## §4. Classification Equivalence -/





/-! ## §5. The Zero Polytope -/


/-! ## §6. Minkowski Addition -/

/-
Minkowski addition: pointwise weight addition, level addition.
-/







/-! ## §7. Convolution on Admissible Characters -/

/-
Convolution: pointwise addition of values, sum of levels.
-/


/-! ## §8. Monoidality: Convolution ↔ Minkowski -/



/-! ## §9. Certified Reconstruction -/










/-! ## §10. Negation (Contragredient) -/




/-! ## §11. Scaling -/

/-
Scale a tropical MV polytope by a natural number.
-/




/-! ## §12. Concrete Tropical Hecke Semimodules -/



/-
Character at base is 0.
-/

/-
Character satisfies edge compatibility.
-/



/-! ## §13. Edge and Plücker Properties -/



/-! ## §14. Pointwise Min/Max Properties -/

/-
Pointwise max preserves edge bounds.
-/

/-
Pointwise min preserves edge bounds.
-/

/-! ## §15. The A₂ Chamber Complex (GL₃) -/






/-! ## §16. Superadditivity -/


/-! ## §17. Reconstruction Injectivity and Surjectivity -/



/-! ## §18. Admissible Sum -/


/-! ## §19. Reconstruction-Minkowski Compatibility -/



open TropicalGeometricLanglandsMV in
theorem solution{C : ChamberComplex ι}
    (k₁ k₂ : ℕ) (χ₁ χ₂ : CharacterOnGenerators ι)
    (h₁ : IsAdmissible C k₁ χ₁) (h₂ : IsAdmissible C k₂ χ₂) :
    IsAdmissible C (k₁ + k₂) (fun i => χ₁ i + χ₂ i) := by
  constructor
  · simp [h₁.1, h₂.1]
  · intro i j hij
    have e1 := h₁.2 i j hij
    have e2 := h₂.2 i j hij
    have : (χ₁ i + χ₂ i) - (χ₁ j + χ₂ j) =
           (χ₁ i - χ₁ j) + (χ₂ i - χ₂ j) := by ring
    rw [this]
    calc (χ₁ i - χ₁ j) + (χ₂ i - χ₂ j)
        ≤ ↑k₁ * C.edgeWeight i j + ↑k₂ * C.edgeWeight i j := add_le_add e1 e2
      _ = (↑k₁ + ↑k₂) * C.edgeWeight i j := by ring
      _ = ↑(k₁ + k₂) * C.edgeWeight i j := by push_cast; ring
