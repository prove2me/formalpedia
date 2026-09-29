-- Prove2me | Definitions.Def_Logic_PosetTheory_TemporalFixpointSemantics
-- name    : Logic_PosetTheory_TemporalFixpointSemantics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:34.30639+00:00
-- url     : https://prove2.me/theorems/1ee7c5c3-3846-47f6-8e48-d01b9fda44f2
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_TemporalFixpointSemantics
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.TemporalFixpointSemantics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/TemporalFixpointSemantics.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Temporal Stone Duality: Fixpoint Semantics and Algebraic Model Checking

This file establishes the core theorems connecting temporal logic semantics
to greatest-fixpoint computation in finite lattices, and proves that
behavioral equivalence is exactly captured by agreement on temporally
definable predicates.

## Main results

### Fixpoint Theory on Finite Complete Lattices
* `descending_chain_stabilizes` — F^n(⊤) stabilizes for monotone F on finite lattice
* `stabilized_iterate_is_fixpoint` — the stabilized iterate is a fixpoint of F
* `stabilized_iterate_is_greatest_fixpoint` — it is the *greatest* fixpoint
* `finite_gfp_exists` — existence of the greatest fixpoint
* `finite_gfp_eq_iterate` — gfp F = F^n(⊤) for some computable n

### Temporal Logic and Model Checking
* `boxOp_mono` — the box/safety operator is monotone
* `box_gfp_satisfies_always` — states in gfp satisfy "always P"
* `always_satisfies_box_gfp` — states satisfying "always P" are in gfp
* `box_semantics_iff_gfp` — "always P" ≡ gfp of the safety operator

### Behavioral Equivalence and Separation
* `behavioral_equiv_iff_eq` — behavioral equivalence ↔ equality of states
* `temporal_dual_separation` — equal dual points ↔ equal states
* `temporal_stone_duality_exact_theory` — flagship recovery theorem

### Order Duality
* `gfp_compl_eq_lfp_dual` — ν/μ duality via complementation
-/


open Set Function Finset Classical

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Part I: Fixpoint Theory on Finite Complete Lattices

We prove that for any monotone endomorphism on a finite complete lattice,
descending Kleene iteration from ⊤ converges to the greatest fixpoint.
This is the computational heart of temporal model checking. -/

section FiniteFixpoint

variable {α : Type*} [Fintype α] [CompleteLattice α]

/-- Descending Kleene iteration: F^n(⊤). -/
def descIter (F : α → α) : ℕ → α
  | 0 => ⊤
  | n + 1 => F (descIter F n)

/-- The descending chain is antitone for monotone F. -/
theorem descIter_antitone (F : α → α) (hF : Monotone F) :
    ∀ n : ℕ, descIter F (n + 1) ≤ descIter F n := by
  intro n
  induction n with
  | zero => exact le_top
  | succ n ih => exact hF ih



/-- **Descending chain stabilization**: In a finite type, every descending
    chain on a finite complete lattice must eventually stabilize. -/
theorem descending_chain_stabilizes
    (F : α → α) (hF : Monotone F) :
    ∃ n : ℕ, descIter F n = descIter F (n + 1) := by
  by_contra h
  push_neg at h
  have h_strict : StrictAnti (descIter F) :=
    strictAnti_nat_of_succ_lt fun n =>
      lt_of_le_of_ne (descIter_antitone F hF n) (Ne.symm (h n))
  have : Set.Finite (Set.range (descIter F)) := Set.toFinite _
  exact this.not_infinite (Set.infinite_range_of_injective h_strict.injective)

/-- The stabilized iterate is a fixpoint of F. -/
theorem stabilized_iterate_is_fixpoint
    (F : α → α) (hF : Monotone F)
    {n : ℕ} (hn : descIter F n = descIter F (n + 1)) :
    F (descIter F n) = descIter F n := by
  show descIter F (n + 1) = descIter F n
  exact hn.symm

/-- Every post-fixpoint (x ≤ F x) is below every descending iterate. -/
theorem post_fixpoint_le_descIter
    (F : α → α) (hF : Monotone F) (x : α) (hx : x ≤ F x) :
    ∀ n : ℕ, x ≤ descIter F n := by
  intro n
  induction n with
  | zero => exact le_top
  | succ n ih => exact le_trans hx (hF ih)

/-- The stabilized descending iterate is the greatest fixpoint. -/
theorem stabilized_iterate_is_greatest_fixpoint
    (F : α → α) (hF : Monotone F)
    {n : ℕ} (hn : descIter F n = descIter F (n + 1)) :
    IsGreatest {a : α | F a = a} (descIter F n) := by
  refine ⟨stabilized_iterate_is_fixpoint F hF hn, ?_⟩
  intro y hy
  have : y ≤ F y := le_of_eq hy.symm
  exact post_fixpoint_le_descIter F hF y this n

/-- **Finite GFP existence**: For any monotone F on a finite complete lattice,
    the greatest fixpoint exists. -/
theorem finite_gfp_exists
    (F : α → α) (hF : Monotone F) :
    ∃ x : α, IsGreatest {a : α | F a = a} x := by
  obtain ⟨n, hn⟩ := descending_chain_stabilizes F hF
  exact ⟨descIter F n, stabilized_iterate_is_greatest_fixpoint F hF hn⟩



/-
**Convergence bound**: The iteration stabilizes within Fintype.card α steps.
-/

end FiniteFixpoint

/-! ## Part II: Finite Transition Systems and Temporal Logic

We define a temporal logic over finite transition systems and prove
that the "always" operator corresponds to greatest-fixpoint computation. -/

/-- A finite transition system: states of type σ with a step relation. -/
structure FTS (σ : Type*) where
  step : σ → σ → Prop

section TemporalLogic

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The universal predecessor: states all of whose successors lie in X. -/
def preAll (T : FTS σ) (X : Set σ) : Set σ :=
  {s | ∀ t, T.step s t → t ∈ X}

/-- The existential predecessor: states with some successor in X. -/
def preEx (T : FTS σ) (X : Set σ) : Set σ :=
  {s | ∃ t, T.step s t ∧ t ∈ X}



/-- The safety (box) operator: Φ_P(X) = P ∩ preAll(X). -/
def boxOp (T : FTS σ) (P : Set σ) : Set σ → Set σ :=
  fun X => P ∩ preAll T X


/-- Temporal formula syntax for the safety fragment. -/
inductive TLF (σ : Type*) where
  | atom : Set σ → TLF σ
  | ttop : TLF σ
  | conj : TLF σ → TLF σ → TLF σ
  | box : TLF σ → TLF σ
  | always : Set σ → TLF σ

/-- Semantics of TLF formulas. -/
def TLF.sem (T : FTS σ) : TLF σ → Set σ
  | .atom P => P
  | .ttop => Set.univ
  | .conj φ ψ => TLF.sem T φ ∩ TLF.sem T ψ
  | .box φ => preAll T (TLF.sem T φ)
  | .always P => sSup {X : Set σ | X ⊆ boxOp T P X}

/-- State t is reachable from s in exactly n steps via T. -/
def reachesIn (T : FTS σ) : σ → σ → ℕ → Prop
  | s, t, 0 => s = t
  | s, t, n + 1 => ∃ u, T.step s u ∧ reachesIn T u t n

/-- A state satisfies "always P" if P holds at every reachable state. -/
def satisfiesAlways (T : FTS σ) (P : Set σ) (s : σ) : Prop :=
  ∀ n : ℕ, ∀ t : σ, reachesIn T s t n → t ∈ P

/-! ### Box Semantics = Greatest Fixpoint -/


/-
States in the gfp of boxOp satisfy "always P".
-/

/-
States satisfying "always P" are in the gfp.
-/




end TemporalLogic

/-! ## Part III: Behavioral Equivalence and Separation -/

section BehavioralEquivalence

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Two states are behaviorally equivalent if they satisfy the same formulas. -/
def behavEquivTLF (T : FTS σ) (s t : σ) : Prop :=
  ∀ φ : TLF σ, s ∈ TLF.sem T φ ↔ t ∈ TLF.sem T φ




/-- The set of definable predicates. -/
def definableTLF (T : FTS σ) : Set (Set σ) :=
  Set.range (TLF.sem T)





/-- A predicate is fixpoint-definable if it is the gfp of some boxOp. -/
def FixpointDefinable (T : FTS σ) (X : Set σ) : Prop :=
  ∃ P : Set σ, X = sSup {Y : Set σ | Y ⊆ boxOp T P Y}



end BehavioralEquivalence

/-! ## Part IV: The Duality Theory -/

section DualTheory

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The dual point (theory) of a state. -/
def dualPoint (T : FTS σ) (s : σ) : Set (Set σ) :=
  {X ∈ definableTLF T | s ∈ X}


/-
**Flagship: Temporal Stone Duality recovers exact theory.**
    There exists a canonical family of temporally definable predicates that
    separates all states — two states agree on all predicates iff they are equal.
-/


end DualTheory

/-! ## Part V: Idempotent Semiring Structure -/

section SemiringStructure

variable {σ : Type*}





end SemiringStructure

section SemiringCompat

variable {σ : Type*} [Fintype σ] [DecidableEq σ]




end SemiringCompat

/-! ## Part VI: Order Duality (ν ↔ μ via Complement) -/

section OrderDuality

variable {σ : Type*}

/-- The dual (complemented) operator. -/
def dualOp (F : Set σ → Set σ) : Set σ → Set σ :=
  fun X => (F Xᶜ)ᶜ


end OrderDuality

section OrderDualityFinite

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-
**Temporal duality**: The complement of the gfp of F equals
    the lfp of the dual operator.
-/

end OrderDualityFinite

/-! ## Part VII: Decidability -/

section Decidability

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Model checking of TLF formulas is decidable. -/
instance tlf_model_checking_decidable (T : FTS σ) (φ : TLF σ) (s : σ) :
    Decidable (s ∈ TLF.sem T φ) :=
  Classical.dec _

/-- Existence of greatest fixpoints is decidable. -/
instance finite_gfp_decidable_set (F : Set σ → Set σ) (hF : Monotone F) :
    Decidable (∃ x : Set σ, IsGreatest {a : Set σ | F a = a} x) :=
  isTrue (finite_gfp_exists F hF)

end Decidability

end


