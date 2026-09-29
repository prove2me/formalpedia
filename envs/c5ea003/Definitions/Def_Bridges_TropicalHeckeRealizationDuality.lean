-- Prove2me | Definitions.Def_Bridges_TropicalHeckeRealizationDuality
-- name    : Bridges_TropicalHeckeRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:27.480498+00:00
-- url     : https://prove2.me/theorems/8590db73-ec81-4b0c-b4ce-d245e2cd29cc
-- title:
--   Aether Catalog definitions — Bridges_TropicalHeckeRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalHeckeRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalHeckeRealizationDuality.lean by skeleton subtraction
import Mathlib
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


namespace TropicalHecke

/-! ## Core Definitions -/

variable {ι Ω S : Type*}

/-- **Tropical associativity** of structure constants `c : ι → ι → ι → S`.

In an idempotent convolution algebra with basis `{e_i}`, the product is defined by
`e_i ⋆ e_j = sup_k (c i j k ⊗ e_k)`. Associativity `(e_i ⋆ e_j) ⋆ e_l = e_i ⋆ (e_j ⋆ e_l)`
translates to the identity:
`sup_n (c i j n ⊗ c n l m) = sup_n (c j l n ⊗ c i n m)` for all `i, j, l, m`.

This is the finite tropical analogue of the associativity constraint on
structure constants of a Hecke algebra. -/
def TropicalAssociative [Fintype ι] [Mul S] [SemilatticeSup S] [OrderBot S]
    (c : ι → ι → ι → S) : Prop :=
  ∀ i j l m, Finset.univ.sup (fun n => c i j n * c n l m) =
              Finset.univ.sup (fun n => c j l n * c i n m)

/-- **Spherical compatibility**: the evaluation matrix `E : Ω → ι → S` satisfies
the tropical eigenfunction equation with respect to structure constants `c`.

For each spherical functional `ω` and basis elements `i, j`:
`E(ω, i) ⊗ E(ω, j) = sup_k (c(i,j,k) ⊗ E(ω, k))`

This says each row of `E` is a simultaneous tropical eigenvector for the
convolution operators defined by `c`. It is the finite tropical analogue of
the spherical function property `φ(g) · φ(h) = ∫ φ(ghk) dk`. -/
def SphericalCompatibility [Fintype ι] [Mul S] [SemilatticeSup S] [OrderBot S]
    (c : ι → ι → ι → S) (E : Ω → ι → S) : Prop :=
  ∀ ω i j, E ω i * E ω j = Finset.univ.sup (fun k => c i j k * E ω k)

/-- **Separation**: basis elements are distinguished by their evaluation profiles.

The map `i ↦ (ω ↦ E(ω, i))` is injective. This is the tropical analogue of
characters separating points in classical harmonic analysis (Gelfand theory). -/
def Separates (E : Ω → ι → S) : Prop :=
  Function.Injective (fun i => fun ω => E ω i)

/-- **Evaluation nondegeneracy**: tropical linear combinations over the basis are
uniquely determined by their evaluations against all spherical functionals.

If `sup_k (a(k) ⊗ E(ω,k)) = sup_k (b(k) ⊗ E(ω,k))` for all `ω`,
then `a = b`.

This is the tropical analogue of linear independence / faithful representation:
the evaluation matrix has enough "rank" to distinguish coefficient vectors. -/
def EvaluationNondegenerate [Fintype ι] [Mul S] [SemilatticeSup S] [OrderBot S]
    (E : Ω → ι → S) : Prop :=
  ∀ a b : ι → S, (∀ ω, Finset.univ.sup (fun k => a k * E ω k) =
                        Finset.univ.sup (fun k => b k * E ω k)) → a = b

/-! ## Bundled Structures -/

/-- A **finite tropical Hecke datum** packages a finite basis type `ι`,
a coefficient semiring `S`, and structure constants `c` defining the
convolution product on basis elements. -/
structure FiniteTropicalHeckeData (S : Type*) [Mul S] [SemilatticeSup S] [OrderBot S] where
  /-- Index type for the Hecke basis -/
  ι : Type*
  [fintype_ι : Fintype ι]
  [decEq_ι : DecidableEq ι]
  /-- Structure constants: `(e_i ⋆ e_j) = sup_k (c i j k ⊗ e_k)` -/
  c : ι → ι → ι → S

attribute [instance] FiniteTropicalHeckeData.fintype_ι FiniteTropicalHeckeData.decEq_ι

/-- A **finite spherical datum** packages evaluation data: a finite family `Ω`
of spherical functionals and their values `eval ω i` on each basis element. -/
structure FiniteSphericalData (S : Type*) where
  /-- Index type for the Hecke basis -/
  ι : Type*
  [fintype_ι : Fintype ι]
  [decEq_ι : DecidableEq ι]
  /-- Index type for spherical functionals -/
  Ω : Type*
  [fintype_Ω : Fintype Ω]
  [decEq_Ω : DecidableEq Ω]
  /-- Evaluation matrix: `eval ω i = φ_ω(e_i)` -/
  eval : Ω → ι → S

attribute [instance] FiniteSphericalData.fintype_ι FiniteSphericalData.decEq_ι
  FiniteSphericalData.fintype_Ω FiniteSphericalData.decEq_Ω

/-! ## Fundamental Lemmas -/



/-! ## Main Reconstruction Theorems -/



/-! ## Evaluation Embedding and Polyhedral Realization -/

/-- The **evaluation embedding** sends each basis element to its profile
of values under all spherical functionals: `i ↦ (ω ↦ E(ω, i))`.

This is the tropical analogue of the Satake transform on basis elements,
mapping coset representatives to their spherical function values. -/
def evaluationEmbedding (E : Ω → ι → S) : ι → (Ω → S) :=
  fun i ω => E ω i



/-! ## Reconstruction from Spherical Data -/

/-- Given spherical data and structure constants, bundled verification that
the data is a valid realization. -/
structure SphericalRealization [Fintype ι] [Mul S] [SemilatticeSup S] [OrderBot S]
    (c : ι → ι → ι → S) (E : Ω → ι → S) where
  /-- The evaluation matrix satisfies spherical compatibility -/
  compatible : SphericalCompatibility c E
  /-- Spherical functionals separate basis elements -/
  separated : Separates E
  /-- The evaluation is nondegenerate -/
  nondegenerate : EvaluationNondegenerate E



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

/-- The **tropical convolution product** on coefficient vectors `ι → S`,
defined by the structure constants `c`. Given vectors `f, g : ι → S`,
their convolution is `(f ⋆ g)(m) = sup_{i,j} f(i) * g(j) * c(i,j,m)`. -/
def tropConv [Fintype ι] [Mul S] [SemilatticeSup S] [OrderBot S]
    (c : ι → ι → ι → S) (f g : ι → S) : ι → S :=
  fun m => (Finset.univ ×ˢ Finset.univ).sup (fun p => f p.1 * g p.2 * c p.1 p.2 m)


/-! ## Summary of the Main Duality -/


end TropicalHecke


