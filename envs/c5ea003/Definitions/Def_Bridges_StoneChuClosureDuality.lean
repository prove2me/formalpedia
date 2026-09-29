-- Prove2me | Definitions.Def_Bridges_StoneChuClosureDuality
-- name    : Bridges_StoneChuClosureDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:51.153067+00:00
-- url     : https://prove2.me/theorems/cad45eb0-703f-413c-8472-df8d10468519
-- title:
--   Aether Catalog definitions — Bridges_StoneChuClosureDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.StoneChuClosureDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/StoneChuClosureDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


/-!
# Stone–Chu Closure Duality for Finite Closure Systems with Observables

This file formalizes a bridge theorem connecting **finite closure systems with
separating observables** to **minimal finite Kripke-style realizations**, establishing
a certified equivalence between closure dynamics and logical realization theory.

## Mathematical Overview

Given a finite type `α` with a closure operator `cl : Set α → Set α` and a finite
family of closure-compatible observables `obs : ι → Set α → Set α`, we define:

- **Observational equivalence** `ObsEquiv cl obs x y`: two elements are equivalent
  when every observable context maps them to the same closed membership.
- **Closed theories**: the set of observable-context / closed-set pairs true at a point.
- **Canonical Kripke realization**: states are equivalence classes under observational
  equivalence, with transitions induced by observables.

## Main Results

* `obsEquiv_equivalence` — Observational equivalence is an equivalence relation.
* `obsEquiv_iff_closedTheory` — Observational equivalence iff equal closed theories.
* `canonicalKripke_obsEquivalent` — The canonical realization is observationally equivalent.
* `canonical_factorization` — Any realization factors through the canonical one.
* `canonicalKripke_minimal` — The canonical realization is minimal.
* `chu_collapse_eq_obsEquiv` — Chu biextensional collapse = observational equivalence.
* `stone_chu_closure_duality` — The flagship duality theorem.
* `reconstruct_minimal_kripke_correct` — Certified reconstruction correctness.
* `exists_minimal_with_iso` — Existence + range-uniqueness of minimal realization.

## Cross-Domain Connections

- **Automata theory / Myhill–Nerode**: `ObsEquiv` is a modal analog of Nerode equivalence;
  the minimal realization is the certified minimal automaton.
- **Coalgebraic modal logic**: The factorization theorem is a minimality statement for
  finite coalgebraic semantics.
- **Formal concept analysis / Chu spaces**: States vs observables form a Chu correspondence;
  closed theories are concept intents, prime classes are extents.
- **Abstract interpretation**: The closure operator is an abstract domain completion;
  the minimal realization is the smallest sound logical machine.
-/

set_option maxHeartbeats 1600000

open Set Function

noncomputable section

namespace StoneChuClosureDuality

/-! ## §1. Closure Operator Axiomatics -/

/-- A closure operator: extensive, monotone, idempotent. -/
structure IsClosureOp {α : Type*} (cl : Set α → Set α) : Prop where
  extensive : ∀ s, s ⊆ cl s
  mono : Monotone cl
  idem : ∀ s, cl (cl s) = cl s

/-- A set is closed if it equals its own closure. -/
def IsClosed' {α : Type*} (cl : Set α → Set α) (s : Set α) : Prop := cl s = s



/-! ## §2. Observable Contexts -/

/-- An observable is closure-compatible if it maps closed sets to closed sets. -/
def ClosureCompatibleObs {α : Type*} (cl : Set α → Set α) (f : Set α → Set α) : Prop :=
  ∀ s, IsClosed' cl s → IsClosed' cl (f s)

/-- Observable context: finite compositions of identity and observables. -/
inductive ObsCtx {α : Type*} {ι : Type*} (obs : ι → Set α → Set α) :
    (Set α → Set α) → Prop where
  | id_ctx : ObsCtx obs id
  | obs_ctx (i : ι) : ObsCtx obs (obs i)
  | comp_ctx {f g : Set α → Set α} : ObsCtx obs f → ObsCtx obs g → ObsCtx obs (f ∘ g)


/-! ## §3. Observational Equivalence -/

/-- Two elements are observationally equivalent if for every observable context `φ`
and every closed set `C`, `x ∈ φ(C)` iff `y ∈ φ(C)`. -/
def ObsEquiv {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) (x y : α) : Prop :=
  ∀ (f : Set α → Set α), ObsCtx obs f → ∀ (C : Set α), IsClosed' cl C →
    (x ∈ f C ↔ y ∈ f C)

theorem obsEquiv_refl {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) (x : α) :
    ObsEquiv cl obs x x :=
  fun _ _ _ _ => Iff.rfl

theorem obsEquiv_symm {α : Type*} {ι : Type*}
    {cl : Set α → Set α} {obs : ι → Set α → Set α} {x y : α}
    (h : ObsEquiv cl obs x y) : ObsEquiv cl obs y x :=
  fun f hf C hC => (h f hf C hC).symm

theorem obsEquiv_trans {α : Type*} {ι : Type*}
    {cl : Set α → Set α} {obs : ι → Set α → Set α} {x y z : α}
    (hxy : ObsEquiv cl obs x y) (hyz : ObsEquiv cl obs y z) :
    ObsEquiv cl obs x z :=
  fun f hf C hC => (hxy f hf C hC).trans (hyz f hf C hC)

/-- Observational equivalence is an equivalence relation. -/
theorem obsEquiv_equivalence {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) :
    Equivalence (ObsEquiv cl obs) :=
  ⟨obsEquiv_refl cl obs, fun h => obsEquiv_symm h, fun h1 h2 => obsEquiv_trans h1 h2⟩

/-- The setoid of observational equivalence. -/
def obsEquivSetoid {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) : Setoid α where
  r := ObsEquiv cl obs
  iseqv := obsEquiv_equivalence cl obs

/-! ## §4. Closed Theories -/

/-- Closed theory membership: `x` is in theory entry `(f, C)` if `f` is an
observable context, `C` is closed, and `x ∈ f(C)`. -/
def ClosedTheoryMem {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α)
    (x : α) (f : Set α → Set α) (C : Set α) : Prop :=
  ObsCtx obs f ∧ IsClosed' cl C ∧ x ∈ f C


/-! ## §5. Congruence Properties -/



/-! ## §6. Finite Quotient -/

/-- The observational equivalence quotient type. -/
def ObsQuotient {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) :=
  Quotient (obsEquivSetoid cl obs)

/-- The canonical map from elements to the quotient. -/
def canonicalMap {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) :
    α → ObsQuotient cl obs :=
  Quotient.mk (obsEquivSetoid cl obs)


/-- The quotient is finite when the base type is finite. -/
instance obsQuotient_finite {α : Type*} {ι : Type*} [Fintype α]
    (cl : Set α → Set α) (obs : ι → Set α → Set α) :
    Finite (ObsQuotient cl obs) :=
  Quotient.finite (obsEquivSetoid cl obs)

/-! ## §7. Kripke Realization -/

/-- A finite Kripke realization for a closure-observable system. -/
structure KripkeRealization {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) (S : Type*) where
  [state_finite : Finite S]
  realize : α → S
  respects_equiv : ∀ x y, ObsEquiv cl obs x y → realize x = realize y
  complete : ∀ x y, realize x = realize y → ObsEquiv cl obs x y

attribute [instance] KripkeRealization.state_finite

/-- The canonical Kripke realization is the observational quotient. -/
def canonicalKripke {α : Type*} {ι : Type*} [Fintype α]
    (cl : Set α → Set α) (obs : ι → Set α → Set α) :
    KripkeRealization cl obs (ObsQuotient cl obs) where
  realize := canonicalMap cl obs
  respects_equiv := fun _ _ h => Quotient.sound h
  complete := fun _ _ h => Quotient.exact h

/-- A realization is observationally equivalent if the realization map
preserves and reflects observational equivalence. -/
def IsObsEquivalent {α : Type*} {ι : Type*}
    {cl : Set α → Set α} {obs : ι → Set α → Set α} {S : Type*}
    (K : KripkeRealization cl obs S) : Prop :=
  ∀ x y : α, ObsEquiv cl obs x y ↔ K.realize x = K.realize y


/-! ## §8. Morphisms and Factorization -/

/-- A morphism between Kripke realizations. -/
structure KripkeHom {α : Type*} {ι : Type*}
    {cl : Set α → Set α} {obs : ι → Set α → Set α}
    {S₁ S₂ : Type*}
    (K₁ : KripkeRealization cl obs S₁)
    (K₂ : KripkeRealization cl obs S₂) where
  toFun : S₁ → S₂
  comm : ∀ x : α, toFun (K₁.realize x) = K₂.realize x

/-- A realization is minimal if it is observationally equivalent and every other
such realization factors through it surjectively. -/
def IsMinimalRealization {α : Type*} {ι : Type*}
    {cl : Set α → Set α} {obs : ι → Set α → Set α} {S : Type*}
    (K : KripkeRealization cl obs S) : Prop :=
  IsObsEquivalent K ∧
  ∀ (T : Type*) (L : KripkeRealization cl obs T), IsObsEquivalent L →
    ∃ f : KripkeHom L K, Surjective f.toFun



/-! ## §9. Uniqueness (isomorphism on range) -/


/-! ## §10. Chu Space Structure -/

/-- A Chu space: states, attributes, and an evaluation relation. -/
structure ChuSpace (S A : Type*) where
  eval : S → A → Prop

/-- Biextensional equivalence: same evaluation profile. -/
def chuStateEquiv {S A : Type*} (chu : ChuSpace S A) (x y : S) : Prop :=
  ∀ a : A, chu.eval x a ↔ chu.eval y a


/-- Attribute type for the closure Chu space. -/
structure ClosureChuAttr (α : Type*) {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) where
  ctx : Set α → Set α
  closedSet : Set α
  ctx_valid : ObsCtx obs ctx
  set_closed : IsClosed' cl closedSet

/-- The Chu space of a closure-observable system. -/
def closureChu {α : Type*} {ι : Type*}
    (cl : Set α → Set α) (obs : ι → Set α → Set α) :
    ChuSpace α (ClosureChuAttr α cl obs) where
  eval x attr := x ∈ attr.ctx attr.closedSet


/-! ## §11. Closed Theory Lattice -/

/-- The closed observable theory of an element. -/
def closedTheoryOf {α : Type*} (cl : Set α → Set α) (x : α) : Set (Set α) :=
  {C | IsClosed' cl C ∧ x ∈ C}



/-! ## §12. Valuation Characterization -/


/-! ## §13. Flagship Duality Theorem -/


/-! ## §14. Algorithmic Reconstruction -/

/-- The reconstruction procedure: compute the minimal Kripke realization. -/
def reconstructMinimalKripke {α : Type*} {ι : Type*} [Fintype α]
    (cl : Set α → Set α) (obs : ι → Set α → Set α) :
    KripkeRealization cl obs (ObsQuotient cl obs) :=
  canonicalKripke cl obs


/-! ## §15. Existence and Range-Uniqueness -/


end StoneChuClosureDuality


