-- Prove2me | solution 1 for OperadicStoneDuality.iso_induces_order_iso
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T22:42:27.31963+00:00
-- url     : https://prove2.me/submissions/271f24d5-d08a-47c7-9834-ce9e9a6a728a

-- Sol generated from Bridges/OperadicStoneDuality.lean
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
theorem principalUpper_infIrred (N : NeuralArchFG) (m : N.Module) :
    InfIrred (UpperSet.Ici m : UpperSet N.Module) := by
  simp +decide

/-
Meet-irreducible upper sets are exactly the principal upper sets.
    Bridge: Algebra (classification of irreducibles) ↔ ML (module identification).
-/
theorem infIrred_iff_principal (N : NeuralArchFG) (U : UpperSet N.Module) :
    InfIrred U ↔ ∃ m : N.Module, U = UpperSet.Ici m := by
  grind +suggestions

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
theorem iso_preserves_infIrred {N M : NeuralArchFG}
    (h : UpperSet N.Module ≃o UpperSet M.Module) (U : UpperSet N.Module) :
    InfIrred U → InfIrred (h U) := by
  unfold InfIrred;
  simp +decide [ IsMax, eq_comm ];
  intro x hx₁ hx₂ hx₃;
  refine' ⟨ ⟨ h x, h.monotone hx₁, _ ⟩, _ ⟩;
  · exact fun h' => hx₂ <| h.le_iff_le.mp h';
  · intro b c hbc;
    have := hx₃ ( show U = h.symm b ⊓ h.symm c from ?_ );
    · cases this <;> simp_all +decide [ ← h.injective.eq_iff ];
    · rw [ ← h.symm_apply_apply U, ← hbc, h.symm.map_inf ]

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





open OperadicStoneDuality in
theorem solution{N M : NeuralArchFG}
    (h : UpperSet N.Module ≃o UpperSet M.Module) :
    ∃ f : N.Module ≃o M.Module,
      ∀ m, h (UpperSet.Ici m) = UpperSet.Ici (f m) := by
  have h_iso : ∀ m : N.Module, ∃ n : M.Module, h (UpperSet.Ici m) = UpperSet.Ici n := by
    have := @iso_preserves_infIrred;
    exact fun m => by have := this h ( UpperSet.Ici m ) ( principalUpper_infIrred N m ) ; rw [ infIrred_iff_principal ] at this; tauto;
  choose f hf using h_iso;
  have h_inj : Function.Injective f := by
    intro m₁ m₂ h_eq;
    have := h.injective ( by aesop : h ( UpperSet.Ici m₁ ) = h ( UpperSet.Ici m₂ ) ) ; aesop;
  have h_surj : Function.Surjective f := by
    have h_surj : ∀ m : M.Module, ∃ n : N.Module, h.symm (UpperSet.Ici m) = UpperSet.Ici n := by
      intro m;
      have := infIrred_iff_principal N ( h.symm ( UpperSet.Ici m ) );
      exact this.mp ( by simpa using iso_preserves_infIrred h.symm _ ( principalUpper_infIrred M m ) );
    intro m; obtain ⟨ n, hn ⟩ := h_surj m; use n; have := h.apply_symm_apply ( UpperSet.Ici m ) ; aesop;
  have h_order_iso : ∀ m₁ m₂ : N.Module, m₁ ≤ m₂ ↔ f m₁ ≤ f m₂ := by
    intros m₁ m₂; exact ⟨fun hmn => by
      have h_order_iso : h (UpperSet.Ici m₁) ≤ h (UpperSet.Ici m₂) := by
        exact h.monotone ( by aesop );
      aesop, fun hmn => by
      have := h.le_iff_le.mp ( show h ( UpperSet.Ici m₁ ) ≤ h ( UpperSet.Ici m₂ ) from by aesop ) ; aesop;⟩;
  refine' ⟨ { Equiv.ofBijective f ⟨ h_inj, h_surj ⟩ with map_rel_iff' := _ }, hf ⟩;
  exact fun { a b } => Iff.symm ( h_order_iso a b )
