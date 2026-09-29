-- Prove2me | Theorems.Thm_OperadicStoneDuality_iso_induces_order_iso
-- name    : OperadicStoneDuality.iso_induces_order_iso
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:59:30.183796+00:00
-- url     : https://prove2.me/theorems/ab9f9851-d432-4e7f-b1f6-82715a4a333b
-- title:
--   Iso induces order iso
-- statement:
--   Formal statement of `OperadicStoneDuality.iso_induces_order_iso` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem OperadicStoneDuality.iso_induces_order_iso{N M : NeuralArchFG}
--       (h : UpperSet N.Module ≃o UpperSet M.Module) :
--       ∃ f : N.Module ≃o M.Module,
--         ∀ m, h (UpperSet.Ici m) = UpperSet.Ici (f m) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/OperadicStoneDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/OperadicStoneDuality.lean#L256

-- Thm stub generated from Bridges/OperadicStoneDuality.lean
import Mathlib
import Definitions.Def_Bridges_OperadicStoneDuality

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

open OperadicStoneDuality

/-! ## Part I: Neural Architecture Foundations -/


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




/-! ## Part VI: Architecture Morphisms and Contravariance -/





/-
**Theorem (Contravariant Functoriality):**
    upperPredMap respects composition contravariantly.
-/

/-
upperPredMap preserves identity.
-/

/-! ## Part VII: Reconstruction Theorem -/


/-
**Key Lemma:** An order isomorphism of upper-set lattices preserves
    meet-irreducibles.
-/

/-
**Key Lemma:** An order isomorphism of upper-set lattices induces
    an order isomorphism of the module posets.
-/

theorem OperadicStoneDuality.iso_induces_order_iso{N M : NeuralArchFG}
    (h : UpperSet N.Module ≃o UpperSet M.Module) :
    ∃ f : N.Module ≃o M.Module,
      ∀ m, h (UpperSet.Ici m) = UpperSet.Ici (f m) := by sorry
