-- Prove2me | Definitions.Def_Bridges_IdempotentHolographicRealization
-- name    : Bridges_IdempotentHolographicRealization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:33.271369+00:00
-- url     : https://prove2.me/theorems/c392957b-5842-4a7b-912b-8b769be49d21
-- title:
--   Aether Catalog definitions — Bridges_IdempotentHolographicRealization
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.IdempotentHolographicRealization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/IdempotentHolographicRealization.lean by skeleton subtraction
import Mathlib

/-!
# Idempotent Holographic Realization via Closure Boundary Semimodules

This file establishes a **bulk–boundary duality theorem** for idempotent computational
systems over commutative semirings, formalizing the principle that boundary observables
plus closure-compatible response data determine the bulk uniquely, minimally, and
canonically.

## Overview

Given a holographic system consisting of:
- A closure operator `c` on a type `X` of bulk states,
- A finite alphabet `Act` of actions with transition maps `T : Act → (X → X)`,
- A boundary observation kernel `K : B → X → S`,
- Boundary probes `xprobe : B → X`,

we define the **boundary response series** and the **closure-refined history equivalence**
(an idempotent Myhill–Nerode relation). The main theorem shows that when the boundary
Hankel rank is finite, the quotient by this equivalence yields a canonical minimal
realization that is unique up to unique isomorphism.

A second theorem shows that **closure-conserved charges** (Noether-style invariants)
descend uniquely to the boundary quotient.

## Application Keywords
tropical Hankel realization, idempotent automata, closure nucleus, EML semantics,
bulk-boundary duality, holographic computation, Myhill-Nerode over semirings,
certified system identification, boundary observability, Noether invariants,
explainable latent states, finite reconstruction, semiring control,
tropical signal processing, categorical holography
-/

open scoped Classical

noncomputable section

/-! ## §1: Closure Operators and Basic Definitions -/

/-- A closure operator on a preordered type: extensive, monotone, idempotent. -/
structure IsClosureOp {X : Type*} [Preorder X] (c : X → X) : Prop where
  extensive : ∀ x, x ≤ c x
  mono : ∀ ⦃x y⦄, x ≤ y → c x ≤ c y
  idem : ∀ x, c (c x) = c x

/-- A state is closed under the closure operator (a fixed point). -/
def ClosedUnder {X : Type*} (c : X → X) (x : X) : Prop := c x = x


/-- Word action: composing transition maps along a list of actions. -/
def wordAction {X Act : Type*} (T : Act → X → X) : List Act → X → X
  | [], x => x
  | a :: w, x => wordAction T w (T a x)




/-! ## §2: Holographic System Structure -/

/-- A holographic system packages bulk states, closure, transitions, kernel, and probes.
    This is the fundamental object encoding a bulk–boundary computational duality. -/
structure HolographicSystem (S : Type*) (Act : Type*) (B : Type*) (X : Type*)
    [CommSemiring S] where
  /-- Closure operator on bulk states -/
  c : X → X
  /-- Transition maps indexed by alphabet -/
  T : Act → X → X
  /-- Boundary observation kernel -/
  K : B → X → S
  /-- Boundary probes mapping boundary elements to bulk states -/
  xprobe : B → X

variable {S : Type*} {Act : Type*} {B : Type*} {X : Type*} [CommSemiring S]

namespace HolographicSystem

/-- The boundary response: observe the result of acting on a probe with a word,
    after applying the closure operator. This is the fundamental observable. -/
def boundaryResponse (sys : HolographicSystem S Act B X)
    (b : B) (w : List Act) (b' : B) : S :=
  sys.K b' (sys.c (wordAction sys.T w (sys.xprobe b)))

/-- The boundary row: the function mapping continuations and outputs to responses,
    given a fixed input probe and history. -/
def boundaryRow (sys : HolographicSystem S Act B X)
    (b : B) (u : List Act) : List Act → B → S :=
  fun w b' => sys.boundaryResponse b (u ++ w) b'

/-- Two histories are equivalent if they produce the same boundary responses
    after closure for all continuations and all boundary outputs.
    This is the closure-refined Myhill–Nerode equivalence. -/
def historyEquiv (sys : HolographicSystem S Act B X) (u v : List Act) : Prop :=
  ∀ (w : List Act) (b : B) (b' : B),
    sys.boundaryResponse b (u ++ w) b' = sys.boundaryResponse b (v ++ w) b'






end HolographicSystem

/-! ## §3: Finite Closure Hankel Rank -/

/-- Finite closure Hankel rank: there exists a finite set of generating histories
    such that every history's boundary row equals some generator's row.
    This is the finiteness condition that enables reconstruction.
    It is the idempotent/tropical analogue of finite Hankel rank in classical
    realization theory. -/
def FiniteClosureHankelRank (sys : HolographicSystem S Act B X) : Prop :=
  ∃ (n : ℕ) (gens : Fin n → B × List Act),
    ∀ (b : B) (u : List Act), ∃ i,
      sys.boundaryRow b u = sys.boundaryRow (gens i).1 (gens i).2

/-! ## §4: The Canonical Minimal Realization -/

/-- The setoid on `B × List Act` induced by boundary row equality. -/
def holographicSetoid (sys : HolographicSystem S Act B X) :
    Setoid (B × List Act) where
  r := fun p q => sys.boundaryRow p.1 p.2 = sys.boundaryRow q.1 q.2
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The minimal realization type: quotient of boundary histories by observational
    equivalence. This is the canonical holographic reconstruction, built entirely
    from boundary data. -/
def HolographicQuotient (sys : HolographicSystem S Act B X) : Type _ :=
  Quotient (holographicSetoid sys)

/-! ## §5: Quotient Operations -/

/-- The canonical projection from histories to the quotient. -/
def holographicProj (sys : HolographicSystem S Act B X)
    (p : B × List Act) : HolographicQuotient sys :=
  Quotient.mk (holographicSetoid sys) p

/-- The reconstructed boundary kernel on the quotient is well-defined:
    equivalent histories produce the same boundary response at the empty
    continuation. -/
def quotientKernel (sys : HolographicSystem S Act B X) (b' : B) :
    HolographicQuotient sys → S :=
  Quotient.lift (fun p => sys.boundaryResponse p.1 p.2 b')
    (fun p q (h : sys.boundaryRow p.1 p.2 = sys.boundaryRow q.1 q.2) => by
      have := congr_fun (congr_fun h []) b'
      simp only [HolographicSystem.boundaryRow, List.append_nil] at this
      exact this)

/-- The transition action on the quotient is well-defined:
    equivalent histories remain equivalent after appending an action. -/
def quotientTransition (sys : HolographicSystem S Act B X) (a : Act) :
    HolographicQuotient sys → HolographicQuotient sys :=
  Quotient.lift (fun p => holographicProj sys (p.1, p.2 ++ [a]))
    (fun p q (h : sys.boundaryRow p.1 p.2 = sys.boundaryRow q.1 q.2) => by
      apply Quotient.sound
      show sys.boundaryRow p.1 (p.2 ++ [a]) = sys.boundaryRow q.1 (q.2 ++ [a])
      ext w b'
      simp only [HolographicSystem.boundaryRow, List.append_assoc]
      exact congr_fun (congr_fun h ([a] ++ w)) b')

/-- Iterated transition from a starting quotient state along a word. -/
def quotientWordAction (sys : HolographicSystem S Act B X) :
    List Act → HolographicQuotient sys → HolographicQuotient sys
  | [], q => q
  | a :: w, q => quotientWordAction sys w (quotientTransition sys a q)





/-! ## §6: Main Reconstruction Theorem -/



/-! ## §7: Closure Charge Descent -/

/-- A closure charge is a function on bulk states that is invariant under
    closure and conserved under closed transitions.
    These are the "Noether charges" of the holographic system. -/
structure ClosureCharge (S : Type*) {Act X : Type*} [CommSemiring S]
    (c : X → X) (T : Act → X → X) where
  /-- The charge function -/
  Q : X → S
  /-- Invariant under closure -/
  closed_inv : ∀ x, Q (c x) = Q x
  /-- Conserved under transitions after closure -/
  transition_inv : ∀ a x, Q (c (T a x)) = Q (c x)

/-- A closure charge is boundary-detectable if it is constant on
    kernel-equivalent closed states. -/
def ClosureCharge.IsBoundaryDetectable
    {S : Type*} {Act B X : Type*} [CommSemiring S]
    {c : X → X} {T : Act → X → X}
    (ch : ClosureCharge S c T) (K : B → X → S) : Prop :=
  ∀ x y, c x = x → c y = y → (∀ b, K b x = K b y) → ch.Q x = ch.Q y

/-- Holographic realization data connecting a bulk system to its boundary quotient.
    This packages the projection map and its compatibility conditions. -/
structure HolographicRealizationData (S : Type*) (Act : Type*) (B : Type*)
    (X : Type*) (Xmin : Type*) [CommSemiring S] where
  /-- Closure on bulk -/
  c : X → X
  /-- Transitions on bulk -/
  T : Act → X → X
  /-- Observation kernel -/
  K : B → X → S
  /-- Projection to minimal realization -/
  proj : X → Xmin
  /-- Transitions on minimal realization -/
  Tmin : Act → Xmin → Xmin
  /-- proj commutes with transitions -/
  proj_tr : ∀ a x, proj (T a x) = Tmin a (proj x)
  /-- proj respects closure -/
  proj_closure : ∀ x, proj (c x) = proj x
  /-- proj surjective -/
  proj_surj : Function.Surjective proj
  /-- Separation: proj identifies the kernel-indistinguishable states after closure -/
  proj_sep : ∀ x y, proj x = proj y → (∀ b, K b (c x) = K b (c y))


/-! ## §8: Boundary Descent Preserves Charge Structure -/

/-- Two closure charges can be added to form a new closure charge. -/
def ClosureCharge.add {S : Type*} {Act X : Type*} [CommSemiring S]
    {c : X → X} {T : Act → X → X}
    (ch1 ch2 : ClosureCharge S c T) : ClosureCharge S c T where
  Q := fun x => ch1.Q x + ch2.Q x
  closed_inv := fun x => by rw [ch1.closed_inv, ch2.closed_inv]
  transition_inv := fun a x => by rw [ch1.transition_inv, ch2.transition_inv]


/-! ## §9: Closure-Compatible Boundary Response Lemma

The boundary response is invariant when we apply closure to the intermediate state.
This is the key compatibility that makes the holographic quotient well-defined. -/


/-! ## §10: Connection to Existing Catalog Results

The `entropy_bound_state_space` theorem from `Bridges/ByzantineCertificate.lean`
provides certified finite-state complexity bounds. In our framework, finite
closure Hankel rank gives a certified upper bound on the number of distinguishable
boundary states, which is the analogue of an entropy bound on the reconstructible
bulk state space.

The `post_quantum_closure_hash_stable` results provide closure-stability under
observational hashing, supporting our claim that the boundary equivalence
relation is stable under closure-compatible compression.

These connections motivate viewing our holographic reconstruction as a
**certified system identification** procedure where boundary complexity
bounds the size of the reconstructible bulk.
-/

end


