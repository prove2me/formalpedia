-- Prove2me | Definitions.Def_Logic_PosetTheory_TemporalStoneSemiringBridge
-- name    : Logic_PosetTheory_TemporalStoneSemiringBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:40.892744+00:00
-- url     : https://prove2.me/theorems/69d740be-86b8-4701-86c0-7f4b4861a7de
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_TemporalStoneSemiringBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.TemporalStoneSemiringBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/TemporalStoneSemiringBridge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Temporal Stone Duality: Recovering Temporal Logic from Idempotent Semiring Fixpoints

This file establishes a precise algebra–logic–computation equivalence theorem:
for a finite transition system whose temporal semantics is encoded by an
idempotent semiring-valued monotone transformer, the clopen semantics on the
Stone spectrum of the fixpoint lattice is *extensionally identical* to the
temporal logic semantics that characterizes behavioral equivalence.

## Main Theorems

### Theorem A: Stone-dual fixpoint lattice recovers temporal equivalence
* `stone_dual_fixpoint_lattice_recovers_temporal_equiv` — two states are
  behaviorally equivalent (agree on all temporal formulas) iff they agree on
  all clopens of the finite Stone dual of the definable-predicate lattice.

### Theorem B: Model checking as greatest-fixpoint computation
* `ltl_model_checking_eq_gfp` — satisfaction of the temporal "always P"
  property is exactly membership in the greatest fixpoint of the safety
  operator X ↦ P ∩ pre(X).

### Theorem C: Finite decidability via iteration stabilization
* `finite_gfp_iteration_stabilizes` — monotone operators on finite powersets
  have descending Kleene chains that stabilize.
* `finite_model_checking_by_iteration` — the always-P semantics equals a
  finitely computed iterate of the safety operator.

### Supporting infrastructure
* Idempotent semiring structure on `Set σ` (union = add, intersection = mul)
* Monotone safety/reachability operators
* Temporal formula language with □, ◇, □*, ◇*
* Behavioral equivalence and dual-point theory
* Complete fixpoint lattice for safety operators
* ν/μ duality via complementation
-/


open Set Function Classical

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Part I: Finite Transition Systems and Predecessor Operators -/

/-- A finite transition system with states of type σ. -/
structure FTS (σ : Type*) where
  /-- The transition relation. -/
  step : σ → σ → Prop

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Universal predecessor: states all of whose successors lie in X. -/
def universalPre (T : FTS σ) (X : Set σ) : Set σ :=
  {s | ∀ t, T.step s t → t ∈ X}

/-- Existential predecessor: states with at least one successor in X. -/
def existentialPre (T : FTS σ) (X : Set σ) : Set σ :=
  {s | ∃ t, T.step s t ∧ t ∈ X}

theorem universalPre_mono (T : FTS σ) : Monotone (universalPre T : Set σ → Set σ) :=
  fun _ _ h s hs t hst => h (hs t hst)




/-! ## Part II: Safety and Reachability Operators -/

/-- The safety operator for "always P": Φ_P(X) = P ∩ universalPre(X). -/
def safetyOp (T : FTS σ) (P : Set σ) (X : Set σ) : Set σ :=
  P ∩ universalPre T X

/-- The reachability operator for "eventually P": Ψ_P(X) = P ∪ existentialPre(X). -/
def reachOp (T : FTS σ) (P : Set σ) (X : Set σ) : Set σ :=
  P ∪ existentialPre T X

theorem safetyOp_mono (T : FTS σ) (P : Set σ) : Monotone (safetyOp T P) :=
  fun _ _ h => Set.inter_subset_inter_right _ (universalPre_mono T h)



/-! ## Part III: Temporal Formula Language -/

/-- Temporal formulas over a finite state space. -/
inductive TFormula : Type where
  | atom : ℕ → TFormula
  | top : TFormula
  | bot : TFormula
  | neg : TFormula → TFormula
  | conj : TFormula → TFormula → TFormula
  | disj : TFormula → TFormula → TFormula
  | box : TFormula → TFormula
  | diamond : TFormula → TFormula
  | always : ℕ → TFormula
  | eventually : ℕ → TFormula
  deriving DecidableEq

/-- Semantics: evaluates a formula to the set of satisfying states. -/
def TFormula.eval (T : FTS σ) (V : ℕ → Set σ) : TFormula → Set σ
  | .atom i => V i
  | .top => Set.univ
  | .bot => ∅
  | .neg φ => (eval T V φ)ᶜ
  | .conj φ ψ => eval T V φ ∩ eval T V ψ
  | .disj φ ψ => eval T V φ ∪ eval T V ψ
  | .box φ => universalPre T (eval T V φ)
  | .diamond φ => existentialPre T (eval T V φ)
  | .always i => sSup {X : Set σ | X ⊆ safetyOp T (V i) X}
  | .eventually i => sInf {X : Set σ | reachOp T (V i) X ⊆ X}

/-! ## Part IV: Behavioral Equivalence and Definable Predicates -/

/-- Two states are behaviorally equivalent if they satisfy the same formulas. -/
def BehavioralEquiv (T : FTS σ) (V : ℕ → Set σ) (s t : σ) : Prop :=
  ∀ φ : TFormula, s ∈ TFormula.eval T V φ ↔ t ∈ TFormula.eval T V φ


/-- The set of temporally definable predicates. -/
def DefinablePreds (T : FTS σ) (V : ℕ → Set σ) : Set (Set σ) :=
  Set.range (TFormula.eval T V)








/-! ## Part V: The Dual Point Map (Finite Stone Spectrum) -/

/-- The dual point of a state: the set of definable predicates containing it. -/
def DualPoint (T : FTS σ) (V : ℕ → Set σ) (s : σ) : Set (Set σ) :=
  {X ∈ DefinablePreds T V | s ∈ X}


/-! ## Part VI: Descending Kleene Iteration and Fixpoint Theory -/

/-- Descending Kleene iteration from ⊤ (= Set.univ). -/
def kleeneDesc (Φ : Set σ → Set σ) : ℕ → Set σ
  | 0 => Set.univ
  | n + 1 => Φ (kleeneDesc Φ n)






/-- The greatest fixpoint as a set. -/
def gfpSet (Φ : Set σ → Set σ) : Set σ :=
  sSup {X : Set σ | X ⊆ Φ X}




/-! ## Part VII: Reachability and "Always P" Semantics -/

/-- Reachability in n steps. -/
def reachesIn (T : FTS σ) : σ → σ → ℕ → Prop
  | s, t, 0 => s = t
  | s, t, n + 1 => ∃ u, T.step s u ∧ reachesIn T u t n

/-- A state satisfies "always P" if P holds at every reachable state. -/
def satisfiesAlways (T : FTS σ) (P : Set σ) (s : σ) : Prop :=
  ∀ n : ℕ, ∀ t : σ, reachesIn T s t n → t ∈ P






/-! ## Part VIII: Idempotent Semiring Structure -/





/-! ## Part IX: ν/μ Duality via Complementation -/

/-- The dual (complemented) operator. -/
def dualOp (F : Set σ → Set σ) : Set σ → Set σ :=
  fun X => (F Xᶜ)ᶜ


/-
The complement of the gfp equals the lfp of the dual operator.
-/

/-! ## Part X: Main Theorems -/







/-- Model checking of temporal formulas is decidable for finite types. -/
noncomputable instance finite_temporal_model_checking_decidable
    (T : FTS σ) (V : ℕ → Set σ) (φ : TFormula) (s : σ) :
    Decidable (s ∈ TFormula.eval T V φ) :=
  Classical.dec _

/-! ## Part XI: Complete Pipeline Theorem -/


/-! ## Part XII: Safety-Reachability Duality -/


/-! ## Part XIII: Fixpoint Lattice Structure -/

/-- The safety operator as an OrderHom. -/
def safetyOrderHom (T : FTS σ) (P : Set σ) : Set σ →o Set σ where
  toFun := safetyOp T P
  monotone' := safetyOp_mono T P

/-- Fixpoints of the safety operator form a complete lattice. -/
noncomputable instance safety_fixpoints_completeLattice (T : FTS σ) (P : Set σ) :
    CompleteLattice (fixedPoints (safetyOrderHom T P)) :=
  inferInstance



end


