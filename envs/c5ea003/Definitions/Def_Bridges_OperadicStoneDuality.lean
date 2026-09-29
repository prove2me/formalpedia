-- Prove2me | Definitions.Def_Bridges_OperadicStoneDuality
-- name    : Bridges_OperadicStoneDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:54.609911+00:00
-- url     : https://prove2.me/theorems/5e934e77-b25b-4b7b-8220-12e2ba85aaa2
-- title:
--   Aether Catalog definitions — Bridges_OperadicStoneDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.OperadicStoneDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/OperadicStoneDuality.lean by skeleton subtraction
import Mathlib

/-!
# Operadic Stone Duality: Neural Heyting Semimodules and
  Certified Architecture–Kripke Reconstruction

Bridge: connects Algebra (distributive lattices, Heyting algebras, Birkhoff duality)
  to Machine Learning (neural architecture identifiability, operadic deep learning)
  to Logic (intuitionistic Kripke semantics, prime filters, bounded morphisms).

## Overview

We prove that finitely generated acyclic neural architectures admit a canonical
intuitionistic semantics — a finite Heyting algebra of *monotone predicates*
(upper sets of the module poset) — from which the architecture can be
reconstructed up to isomorphism.

The upper set lattice `UpperSet N.Module` is a finite distributive lattice
and Heyting algebra. Its join-irreducible elements are the principal upper sets
`↑m = Ici m`, which correspond bijectively to modules. The module partial order
is recovered via `m₁ ≤ m₂ ↔ Ici m₁ ≤ Ici m₂` (in the UpperSet order).

An order isomorphism of upper-set lattices therefore induces an order isomorphism
of module posets, establishing the reconstruction theorem.

## Main Results

* `pred_distrib_lattice` — upper sets form a distributive lattice
* `pred_heyting` — upper sets form a Heyting algebra
* `pred_finite` — the lattice is finite
* `ici_orderEmbedding` — m ↦ Ici m is an order embedding
* `principalUpper_joinIrred` — principal upper sets are join-irreducible
* `joinIrred_iff_principal` — join-irreducibles = principal upper sets
* `soundness_completeness` — lattice order = Kripke semantic entailment
* `upperPredMap_contravariant` — contravariant functoriality
* `iso_induces_order_iso` — upper-set lattice iso ⟹ module order iso
* `semantics_determines_architecture` — the main reconstruction theorem
-/

open Set Function

noncomputable section

namespace OperadicStoneDuality

/-! ## Part I: Neural Architecture Foundations -/

/-- A finitely generated acyclic neural architecture.
    Bridge: ML (neural architecture) ↔ Algebra (finite partial order). -/
structure NeuralArchFG where
  /-- The type of modules/layers -/
  Module : Type
  [instFintype : Fintype Module]
  [instDecEq : DecidableEq Module]
  [instPartialOrder : PartialOrder Module]
  /-- The primitive generators -/
  generators : Finset Module
  /-- Every module is above some generator -/
  generation : ∀ m : Module, ∃ g ∈ generators, g ≤ m
  /-- Generators are nonempty -/
  gen_nonempty : generators.Nonempty

attribute [instance] NeuralArchFG.instFintype NeuralArchFG.instDecEq
  NeuralArchFG.instPartialOrder

/-! ## Part II: Upper Set Predicate Lattice

We use Mathlib's `UpperSet α` — the type of upward-closed subsets of a
preordered type. For a finite partial order, this is automatically:
- a distributive lattice (`DistribLattice`)
- a Heyting algebra (`HeytingAlgebra`)
- finite (`Finite`)

The ordering on `UpperSet α` is: `U ≤ V ↔ V.carrier ⊆ U.carrier` (reverse
inclusion). This means `Ici m₁ ≤ Ici m₂ ↔ m₁ ≤ m₂`, so the map `m ↦ Ici m`
is an order embedding. -/

/-- The predicate lattice is a distributive lattice. -/
instance pred_distrib_lattice (N : NeuralArchFG) :
    DistribLattice (UpperSet N.Module) := inferInstance

/-- The predicate lattice is a Heyting algebra. -/
instance pred_heyting (N : NeuralArchFG) :
    HeytingAlgebra (UpperSet N.Module) := inferInstance


/-! ## Part III: Principal Upper Sets and Order Embedding

The map `m ↦ Ici m` sends modules to their principal upper sets.
This is an order embedding, meaning the module partial order is
faithfully encoded in the upper set lattice. -/

/-
The principal upper set map is an order embedding.
    This is the key structural fact: the module order is encoded
    in the upper-set lattice order.

    Bridge: Order theory (Birkhoff embedding) ↔ ML (architecture encoding).
-/

/-
The map `m ↦ Ici m` is injective.
    Bridge: Algebra (separation).
-/


/-! ## Part IV: Join-Irreducibles

An element of a bounded lattice is join-irreducible if it's nonzero and
cannot be written as a non-trivial join. The join-irreducibles of
`UpperSet α` are exactly the principal upper sets `Ici m`. -/

/-
Principal upper sets are meet-irreducible (`InfIrred`) in the upper set lattice.
    In Mathlib's `UpperSet`, `⊓ = ∪` and `⊔ = ∩`, so meet-irreducibility means
    `Ici m` cannot be written as `A ∪ B` for strictly larger `A`, `B`.

    Proof: if `Ici m = A ∪ B` then `m ∈ A` or `m ∈ B`. WLOG `m ∈ A`.
    Since `A` is upper, `Ici m ⊆ A ⊆ A ∪ B = Ici m`, so `A = Ici m`.

    Bridge: Algebra (meet-irreducible) ↔ ML (atomic module).
-/

/-
Meet-irreducible upper sets are exactly the principal upper sets.
    Bridge: Algebra (classification of irreducibles) ↔ ML (module identification).
-/

/-
The meet-irreducibles biject with modules.
-/

/-! ## Part V: Soundness and Completeness -/

/-- Kripke forcing: world w forces proposition U iff w ∈ U. -/
def kforces (N : NeuralArchFG) (w : N.Module) (U : UpperSet N.Module) : Prop :=
  w ∈ U

/-- Semantic entailment: V entails U means every world in V is also in U.
    Note: In the `UpperSet` order, `U ≤ V` means `V ⊆ U` as sets,
    so `U ≤ V` means V entails U (V is stronger than U). -/
def ksemEntails (N : NeuralArchFG) (V U : UpperSet N.Module) : Prop :=
  ∀ w, kforces N w V → kforces N w U


/-! ## Part VI: Architecture Morphisms and Contravariance -/

/-- A morphism of neural architectures. -/
structure NeuralArchHom (N M : NeuralArchFG) where
  toFun : N.Module → M.Module
  monotone : Monotone toFun
  gen_map : ∀ g ∈ N.generators, toFun g ∈ M.generators

/-- The inverse image map on upper-set predicates.
    Bridge: Algebra (contravariant functor) ↔ Logic (substitution). -/
def upperPredMap {N M : NeuralArchFG} (f : NeuralArchHom N M) :
    UpperSet M.Module → UpperSet N.Module :=
  fun U => ⟨f.toFun ⁻¹' (U : Set M.Module),
    fun _ _ hxy hx => U.upper (f.monotone hxy) hx⟩

/-- Identity morphism. -/
def neuralArchId (N : NeuralArchFG) : NeuralArchHom N N where
  toFun := id
  monotone := fun _ _ h => h
  gen_map := fun _ hg => hg

/-- Composition of morphisms. -/
def neuralArchComp {N M P : NeuralArchFG}
    (f : NeuralArchHom N M) (g : NeuralArchHom M P) : NeuralArchHom N P where
  toFun := g.toFun ∘ f.toFun
  monotone := fun _ _ h => g.monotone (f.monotone h)
  gen_map := fun gen hgen => g.gen_map _ (f.gen_map gen hgen)

/-
**Theorem (Contravariant Functoriality):**
    upperPredMap respects composition contravariantly.
-/

/-
upperPredMap preserves identity.
-/

/-! ## Part VII: Reconstruction Theorem -/

/-- Two architectures are isomorphic. -/
def NeuralArchIso (N M : NeuralArchFG) : Prop :=
  ∃ f : N.Module ≃o M.Module,
    (∀ g, g ∈ N.generators → f g ∈ M.generators) ∧
    (∀ g, g ∈ M.generators → f.symm g ∈ N.generators)

/-
**Key Lemma:** An order isomorphism of upper-set lattices preserves
    meet-irreducibles.
-/

/-
**Key Lemma:** An order isomorphism of upper-set lattices induces
    an order isomorphism of the module posets.
-/

/-
**Main Theorem (Semantics Determines Architecture):**
    If two architectures have isomorphic upper-set predicate lattices,
    and the isomorphism preserves generator-marking, then the architectures
    are isomorphic.

    Bridge: ML (architecture identifiability) ↔ Algebra (lattice determines poset)
    ↔ Logic (semantics determines syntax).
-/

/-! ## Part VIII: Persistence -/


/-! ## Part IX: Semimodule Enrichment -/


/-! ## Part X: Concrete Examples -/



end OperadicStoneDuality


