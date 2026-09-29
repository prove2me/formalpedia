-- Prove2me | Definitions.Def_Bridges_IdempotentThermodynamicRealization
-- name    : Bridges_IdempotentThermodynamicRealization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:32.006833+00:00
-- url     : https://prove2.me/theorems/29656067-ea66-496a-8ccb-4e18ba3bb9de
-- title:
--   Aether Catalog definitions — Bridges_IdempotentThermodynamicRealization
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.IdempotentThermodynamicRealization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/IdempotentThermodynamicRealization.lean by skeleton subtraction
import Mathlib
/-
# Idempotent Thermodynamic Realization via Closure Entropy and Free-Energy Minimization

This file formalizes a **thermodynamic Myhill–Nerode theorem**: a canonical minimization
principle for deterministic automata with observable outputs, where "observation" is
mediated by a closure operator and an entropy functional, and the free-energy observable
determines the finest useful state equivalence.

## Main Results

- `wordEquiv_right_congruence` — Free-energy indistinguishability is a right congruence.
- `thermoState_finite` — The quotient by behavioral equivalence has finitely many states.
- `quotientAut_behavior_eq` — The quotient automaton realizes the same behavior.
- `quotientAut_minimal` — The quotient is minimal among all behaviorally equivalent automata.
- `gibbsHankelRank_eq_card_thermoState` — The Gibbs–Hankel generator rank equals the
  number of quotient states.
- `freeEnergy_min_commutes_closure` — Free-energy minimization commutes with closure
  saturation.
- `optimal_paths_same_dissipation` — Optimal paths share a conserved dissipation class.

## Bridges

- **Automata Theory ↔ Tropical Algebra**: Myhill–Nerode via idempotent free energy
- **Statistical Mechanics ↔ Computation**: Free energy as canonical observable
- **Closure Semantics ↔ Minimization**: Coarse-graining commutes with optimization
- **EML ↔ Tropical Geometry**: Generator rank = tropical dimension of computation
-/


open Function List Classical

noncomputable section

namespace Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization

/-! ## §1. Thermodynamic Automaton: Core Structure -/

/-- A thermodynamic automaton: a deterministic finite automaton with an observable
    output function `obs : Q → S`. The output captures the "free-energy observable"
    at each state, abstracting the formula `β * H_C(C(summary(q)))`. -/
structure ThermoAut (S : Type*) (σ : Type*) (Q : Type*) where
  init : Q
  step : Q → σ → Q
  obs : Q → S

variable {S σ Q : Type*}

/-! ## §2. Running the Automaton on Words -/

/-- Extend the transition function to words (lists of symbols). -/
def ThermoAut.run (A : ThermoAut S σ Q) : Q → List σ → Q
  | q, [] => q
  | q, a :: w => A.run (A.step q a) w




/-! ## §3. Behavior and Residuals -/

/-- The global behavior: maps each word to its observable output. -/
def ThermoAut.behavior (A : ThermoAut S σ Q) : List σ → S :=
  fun w => A.obs (A.run A.init w)

/-- The residual behavior from state `q`: continuations mapped to outputs. -/
def ThermoAut.residual (A : ThermoAut S σ Q) (q : Q) : List σ → S :=
  fun w => A.obs (A.run q w)



/-! ## §4. State Behavioral Equivalence (Thermodynamic Equivalence) -/

/-- Two states are **thermodynamically equivalent** if they produce the same output
    on every continuation. -/
def ThermoAut.stateEquiv (A : ThermoAut S σ Q) (q₁ q₂ : Q) : Prop :=
  A.residual q₁ = A.residual q₂

theorem ThermoAut.stateEquiv_iff (A : ThermoAut S σ Q) (q₁ q₂ : Q) :
    A.stateEquiv q₁ q₂ ↔ ∀ w : List σ, A.obs (A.run q₁ w) = A.obs (A.run q₂ w) := by
  simp [stateEquiv, residual, funext_iff]

def ThermoAut.stateSetoid (A : ThermoAut S σ Q) : Setoid Q where
  r := A.stateEquiv
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Thermodynamic equivalence is compatible with transitions. -/
theorem ThermoAut.stateEquiv_step (A : ThermoAut S σ Q) {q₁ q₂ : Q} (a : σ)
    (h : A.stateEquiv q₁ q₂) : A.stateEquiv (A.step q₁ a) (A.step q₂ a) := by
  rw [stateEquiv_iff] at *; intro w; exact h (a :: w)

/-- Equivalent states have the same observation. -/
theorem ThermoAut.stateEquiv_obs (A : ThermoAut S σ Q) {q₁ q₂ : Q}
    (h : A.stateEquiv q₁ q₂) : A.obs q₁ = A.obs q₂ := by
  have := (A.stateEquiv_iff q₁ q₂).mp h []; simpa using this


/-! ## §5. Word-Level Indistinguishability -/

/-- Two words are **free-energy indistinguishable** if they lead to states with
    the same residual behavior. -/
def ThermoAut.wordEquiv (A : ThermoAut S σ Q) (u v : List σ) : Prop :=
  A.stateEquiv (A.run A.init u) (A.run A.init v)



/-! ## §6. Right Congruence -/



/-! ## §7. Quotient State Space (Thermodynamic States) -/

/-- The quotient of Q by thermodynamic equivalence. -/
def ThermoState (A : ThermoAut S σ Q) : Type _ := Quotient A.stateSetoid

instance thermoState_finite [Finite Q] (A : ThermoAut S σ Q) :
    Finite (ThermoState A) := Quotient.finite _

noncomputable instance thermoState_fintype [Fintype Q]
    (A : ThermoAut S σ Q) : Fintype (ThermoState A) :=
  @Quotient.fintype _ _ A.stateSetoid (Classical.decRel _)

/-! ## §8. Quotient Automaton Construction -/

/-- The **thermodynamic quotient automaton**: minimal realization by
    identifying behaviorally equivalent states. -/
noncomputable def ThermoAut.quotientAut (A : ThermoAut S σ Q) :
    ThermoAut S σ (ThermoState A) where
  init := @Quotient.mk _ A.stateSetoid A.init
  step := fun q a =>
    @Quotient.lift _ _ A.stateSetoid
      (fun q' => @Quotient.mk _ A.stateSetoid (A.step q' a))
      (fun _ _ h => Quotient.sound (A.stateEquiv_step a h)) q
  obs := fun q =>
    @Quotient.lift _ _ A.stateSetoid A.obs
      (fun _ _ h => A.stateEquiv_obs h) q




/-! ## §9. Behavior Preservation -/


/-! ## §10. Minimality of the Quotient Automaton -/

/-
**Minimality theorem**: if automaton `B` with state space `Q'` has the same
    global behavior as `A`, then `A`'s quotient has at most `|Q'|` states.

    Key insight: if two words reach the same B-state, they produce the same output
    on all continuations (since behaviors agree), hence are in the same A-equivalence class.
    So distinct A-classes map to distinct B-states.
-/

/-! ## §11. Free-Energy Specific Definitions -/

variable {Obs : Type*}

/-- Construct a ThermoAut from closure-enriched data:
    `obs(q) = β * Hc(C(summary(q)))`. -/
def mkThermoAut [Mul S] (init : Q) (step : Q → σ → Q) (summary : Q → Obs)
    (C : Obs → Obs) (Hc : Obs → S) (β : S) : ThermoAut S σ Q where
  init := init
  step := step
  obs := fun q => β * Hc (C (summary q))

/-- Free-energy indistinguishability with explicit closure structure. -/
def freeEnergyIndistinguishable [Mul S] (init : Q) (step : Q → σ → Q)
    (summary : Q → Obs) (C : Obs → Obs) (Hc : Obs → S) (β : S)
    (u v : List σ) : Prop :=
  (mkThermoAut init step summary C Hc β).wordEquiv u v



/-! ## §12. Gibbs–Hankel Semimodule and Generator Rank -/

/-- The Gibbs–Hankel row of a state: its residual function. -/
def ThermoAut.gibbsHankelRow (A : ThermoAut S σ Q) (q : Q) : List σ → S :=
  A.residual q


/-- The set of distinct Gibbs–Hankel rows. -/
noncomputable def ThermoAut.gibbsHankelRows [Fintype Q]
    (A : ThermoAut S σ Q) : Finset (List σ → S) :=
  Finset.univ.image A.gibbsHankelRow

/-- **Gibbs–Hankel generator rank**: the number of distinct behavioral profiles. -/
noncomputable def ThermoAut.gibbsHankelGeneratorRank [Fintype Q]
    (A : ThermoAut S σ Q) : ℕ :=
  A.gibbsHankelRows.card

/-
**Rank–state equality**: the Gibbs–Hankel generator rank equals the number
    of thermodynamic states.
-/

/-! ## §13. Uniqueness Up to Isomorphism -/

/-- An isomorphism between thermodynamic automata. -/
structure ThermoAutIso (A : ThermoAut S σ Q) {Q' : Type*} (B : ThermoAut S σ Q') where
  toEquiv : Q ≃ Q'
  init_map : toEquiv A.init = B.init
  step_map : ∀ q a, toEquiv (A.step q a) = B.step (toEquiv q) a
  obs_map : ∀ q, A.obs q = B.obs (toEquiv q)

/-- A thermodynamic automaton is a **minimal realization** if no two distinct
    states are behaviorally equivalent. -/
def ThermoAut.IsMinimalRealization (A : ThermoAut S σ Q) : Prop :=
  ∀ q₁ q₂ : Q, A.stateEquiv q₁ q₂ → q₁ = q₂

/-
**Uniqueness of minimal realizations**: any two minimal realizations with the
    same behavior are isomorphic (assuming all states are reachable).
-/

/-! ## §14. Closure–Minimization Commutation -/

/-- A closure operator on Obs. -/
structure ClosureOp (Obs : Type*) [Preorder Obs] where
  cl : Obs → Obs
  extensive : ∀ o, o ≤ cl o
  monotone : ∀ {o₁ o₂}, o₁ ≤ o₂ → cl o₁ ≤ cl o₂
  idempotent : ∀ o, cl (cl o) = cl o

/-- Entropy is closure-invariant. -/
def ClosureEntropySubmodular [Preorder Obs] (C : ClosureOp Obs) (Hc : Obs → S) : Prop :=
  ∀ o, Hc (C.cl o) = Hc o

/-- The closure-saturated automaton. -/
def closureSaturatedAut [Mul S] [Preorder Obs]
    (init : Q) (step : Q → σ → Q) (summary : Q → Obs)
    (C : ClosureOp Obs) (Hc : Obs → S) (β : S) : ThermoAut S σ Q :=
  mkThermoAut init step (fun q => C.cl (summary q)) C.cl Hc β

/-
**Closure–minimization commutation**: when entropy is closure-invariant,
    the original and closure-saturated automata have the same behavior.
-/

/-! ## §15. Dissipation Classes and Conservation -/

/-- A dissipation class labels a state with a coarse-grained observable. -/
structure DissipationClass (S : Type*) where
  label : S
  deriving DecidableEq

def ThermoAut.wordDissipation (A : ThermoAut S σ Q) (w : List σ) : DissipationClass S :=
  ⟨A.obs (A.run A.init w)⟩

/-- A word is **optimal** if its observation is ≤ all same-length words'. -/
def ThermoAut.IsOptimalPath [Preorder S] (A : ThermoAut S σ Q) (w : List σ) : Prop :=
  ∀ w' : List σ, w'.length = w.length → A.obs (A.run A.init w) ≤ A.obs (A.run A.init w')

/-
**Conservation of dissipation class** for optimal paths of the same length.
-/

/-! ## §16. Certified Minimization -/

/-
**Existence of certified minimization**: the quotient construction provides
    a minimal realization for any thermodynamic automaton.
-/

/-! ## §17. Auxiliary Lemmas -/

def ThermoAut.reachableStates (A : ThermoAut S σ Q) : Set Q :=
  {q | ∃ w : List σ, A.run A.init w = q}




/-! ## §18. Closure Invariance -/


end Bridges.AlgebraEMLComputation.IdempotentThermodynamicRealization


