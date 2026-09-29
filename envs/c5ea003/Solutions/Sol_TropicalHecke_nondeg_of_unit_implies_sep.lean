-- Prove2me | solution 1 for TropicalHecke.nondeg_of_unit_implies_sep
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:28.95961+00:00
-- url     : https://prove2.me/submissions/0ba2e4f1-c150-4b46-8eb6-24738939c269

-- Sol generated from Bridges/TropicalHeckeRealizationDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalHeckeRealizationDuality
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Harmonic / Aristotle

# Tropical Hecke Realization Duality via Idempotent Convolution Semimodules

This file formalizes a **finite tropical Hecke reconstruction theorem**:
finitely generated idempotent convolution algebras with structure constants are
uniquely determined by their evaluation against tropical spherical functionals,
provided a separation and nondegeneracy condition holds.

## Main Results

* `TropicalHecke.constants_determined_by_eval` — Two sets of structure constants
  compatible with the same evaluation matrix must be equal under nondegeneracy.
* `TropicalHecke.finite_tropical_hecke_realization_duality` — The main ∃! theorem:
  there exists a unique set of structure constants compatible with given evaluation data.
* `TropicalHecke.finite_tropical_satake_realization` — The evaluation embedding
  faithfully realizes Hecke data in tropical affine space.
* `TropicalHecke.reconstruction_from_spherical_data` — Spherical data satisfying
  compatibility uniquely reconstructs the underlying Hecke algebra.

## Mathematical Context

In classical representation theory, the Satake isomorphism identifies the spherical
Hecke algebra with a ring of characters. Our finite tropical analogue replaces:
- the Hecke algebra with an idempotent convolution algebra defined by structure constants,
- characters with tropical spherical functionals (evaluation against basis elements),
- the Satake transform with the evaluation embedding into tropical affine space.

The reconstruction theorem says: if the spherical functionals separate basis elements
and the evaluation matrix is nondegenerate (tropical linear combinations are determined
by their evaluations), then the structure constants — and hence the entire algebra —
are uniquely determined by the evaluation data.

## References

This formalizes ideas from tropical geometry, idempotent analysis, and finite
harmonic analysis, creating a bridge between tropical algebra and representation theory.
-/


open TropicalHecke

/-! ## Core Definitions -/

variable {ι Ω S : Type*}





/-! ## Bundled Structures -/


attribute [instance] FiniteTropicalHeckeData.fintype_ι FiniteTropicalHeckeData.decEq_ι


attribute [instance] FiniteSphericalData.fintype_ι FiniteSphericalData.decEq_ι
  FiniteSphericalData.fintype_Ω FiniteSphericalData.decEq_Ω

/-! ## Fundamental Lemmas -/



/-! ## Main Reconstruction Theorems -/



/-! ## Evaluation Embedding and Polyhedral Realization -/




/-! ## Reconstruction from Spherical Data -/




/-! ## Spherical Compatibility Preserves Structure -/


/-! ## Pointwise Product Characterization -/


/-! ## Derived Corollaries -/


/-! ## Finite Tropical Satake Realization -/


/-! ## Commutativity Transfer -/


/-! ## Nondegeneracy Implies Separation -/


/-! ## Composition of Realizations -/


/-! ## Associativity Forced by Nondegeneracy -/


/-! ## Evaluation Matrix Factorization -/


/-! ## Reconstruction Identity -/


/-! ## Tropical Plancherel-Type Theorem -/


/-! ## Idempotent Convolution Product -/



/-! ## Summary of the Main Duality -/



open TropicalHecke in
theorem solution    [Fintype ι] [DecidableEq ι] [MulOneClass S] [SemilatticeSup S] [OrderBot S]
    {E : Ω → ι → S}
    (h_nondeg : EvaluationNondegenerate E)
    (h_one_ne_bot : (1 : S) ≠ ⊥)
    (h_unit : ∀ (i : ι) (ω : Ω),
      Finset.univ.sup (fun k => (if k = i then 1 else ⊥) * E ω k) = E ω i) :
    Separates E := by
  intro i j h_eq
  have key : (fun k => if k = i then (1 : S) else ⊥) =
             (fun k => if k = j then (1 : S) else ⊥) := by
    apply h_nondeg
    intro ω
    rw [h_unit i, h_unit j]
    exact congr_fun h_eq ω
  by_contra h_ne
  have h1 := congr_fun key i
  simp [h_ne] at h1
  exact h_one_ne_bot h1
