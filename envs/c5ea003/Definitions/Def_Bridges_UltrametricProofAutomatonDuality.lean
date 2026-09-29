-- Prove2me | Definitions.Def_Bridges_UltrametricProofAutomatonDuality
-- name    : Bridges_UltrametricProofAutomatonDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:40.157569+00:00
-- url     : https://prove2.me/theorems/610cee24-c740-4ada-9d87-82907dade194
-- title:
--   Aether Catalog definitions — Bridges_UltrametricProofAutomatonDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricProofAutomatonDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricProofAutomatonDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Ultrametric Proof Automaton Duality via Observer-Trace Congruences

This file formalizes a duality between **ultrametric proof dynamics** and
**minimal deterministic proof automata** via observer-trace congruences,
building on the Myhill–Nerode pattern from `ProofCongruenceAutomata` and
prime-state reconstruction from `EMLSpectralSemantics`.

## Core Idea

Given a finite proof system with states `P`, contraction alphabet `A`,
observers `O`, and observer evaluation `obs : O → P → S`, we define
**observational equivalence** as agreement of all observer evaluations under all
contraction words, show it is a congruence, identify it with the kernel of a
canonical trace morphism, construct a minimal quotient automaton, and prove uniqueness.

## Main Results

* `obsEquiv_is_equivalence` — observational equiv is an equivalence relation
* `observational_equiv_is_congruence` — congruence under contractions
* `observational_equiv_eq_kernel` — equivalence = kernel of trace map
* `quotient_step_wellDefined` — contraction action descends to the quotient
* `repr_eq_implies_equiv` — representation injectivity implies minimality
* `canonical_factors_through` — canonical automaton has universal property
* `ultrametric_isosceles` — non-Archimedean isosceles triangle theorem
* `ultrametric_zero_equiv` — distance-zero is an equivalence relation
* `finite_duality_theorem` — the full duality packaging
* `traceImage_closed_under_residual` — trace image is a residual sub-semimodule
* `obsSep_isUltrametric` — observer separation is ultrametric

**application keywords:** non-Archimedean automata, ultrametric proof dynamics,
Myhill–Nerode duality, idempotent semimodules, tropical logic, residual automata,
proof-state minimization, certified reconstruction, prime-congruence semantics,
abstract interpretation, formal learning theory, proof compression.
-/


set_option maxHeartbeats 800000

open Function

noncomputable section

namespace UltrametricProofAutomaton

/-! ## §1. Running Contraction Words -/

/-- Apply a word of contraction symbols to a proof state, left-to-right. -/
def runWord {P A : Type*} (step : A → P → P) : List A → P → P
  | [], p => p
  | a :: w, p => runWord step w (step a p)




/-! ## §2. Observational Equivalence -/

/-- Observational equivalence: `p ≈ q` iff for every contraction word `w` and
every observer `o`, the observer evaluations agree.
Bridge: proof-theoretic analogue of Myhill–Nerode right-congruence. -/
def obsEquiv {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) (p q : P) : Prop :=
  ∀ (w : List A) (o : O), obs o (runWord step w p) = obs o (runWord step w q)

theorem obsEquiv_refl {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) (p : P) :
    obsEquiv step obs p p := fun _ _ => rfl

theorem obsEquiv_symm {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) {p q : P}
    (h : obsEquiv step obs p q) : obsEquiv step obs q p :=
  fun w o => (h w o).symm

theorem obsEquiv_trans {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) {p q r : P}
    (hpq : obsEquiv step obs p q) (hqr : obsEquiv step obs q r) :
    obsEquiv step obs p r :=
  fun w o => (hpq w o).trans (hqr w o)

/-- Observational equivalence is an equivalence relation. -/
theorem obsEquiv_is_equivalence {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) :
    Equivalence (obsEquiv step obs : P → P → Prop) :=
  ⟨obsEquiv_refl step obs,
   fun h => obsEquiv_symm step obs h,
   fun h₁ h₂ => obsEquiv_trans step obs h₁ h₂⟩

/-- The setoid induced by observational equivalence. -/
def obsSetoid (P : Type*) {A O S : Type*}
    (step : A → P → P) (obs : O → P → S) : Setoid P where
  r := obsEquiv step obs
  iseqv := obsEquiv_is_equivalence step obs

/-! ## §3. Congruence Property -/

/-- **Key congruence theorem**: Observational equivalence is preserved by
contraction steps. If `p ≈ q` then `step a p ≈ step a q`.
Bridge: the proof-system analogue of right-invariance in Myhill–Nerode theory. -/
theorem observational_equiv_is_congruence {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S)
    {p q : P} (h : obsEquiv step obs p q) (a : A) :
    obsEquiv step obs (step a p) (step a q) :=
  fun w o => h (a :: w) o


/-! ## §4. Observer Trace Space and Kernel Theorem -/

/-- Build the trace profile of a proof state. -/
def buildTrace {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) (p : P) :
    List A × O → S :=
  fun ⟨w, o⟩ => obs o (runWord step w p)


/-! ## §5. Quotient Automaton Construction -/

/-- The quotient type of proof states by observational equivalence. -/
abbrev StateQuotient (P : Type*) {A O S : Type*}
    (step : A → P → P) (obs : O → P → S) :=
  Quotient (obsSetoid P step obs)


/-- The descended contraction action on quotient states. -/
def quotientStep {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) (a : A) :
    StateQuotient P step obs → StateQuotient P step obs :=
  Quotient.map (step a) (fun _ _ h => observational_equiv_is_congruence step obs h a)

/-- Observer evaluation descends to the quotient. -/
def quotientObs {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) (o : O) :
    StateQuotient P step obs → S :=
  Quotient.lift (obs o) (fun _ _ h => h [] o)

/-! ## §6. Deterministic Proof Automaton -/

/-- A deterministic proof automaton. -/
structure DetProofAutomaton (A O S Q : Type*) where
  transition : A → Q → Q
  output : O → Q → S

/-- The canonical minimal automaton from the quotient. -/
def canonicalAut {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) :
    DetProofAutomaton A O S (StateQuotient P step obs) where
  transition := quotientStep step obs
  output := quotientObs step obs


/-! ## §7. Representation and Minimality -/

/-- A representation from proof states to automaton states. -/
def IsRepr {P A O S Q : Type*}
    (step : A → P → P) (obs : O → P → S)
    (aut : DetProofAutomaton A O S Q) (repr : P → Q) : Prop :=
  (∀ a p, repr (step a p) = aut.transition a (repr p)) ∧
  (∀ o p, obs o p = aut.output o (repr p))



/-- Run a word through an automaton's transition function. -/
def runWordAut {A Q : Type*} (trans : A → Q → Q) : List A → Q → Q
  | [], q => q
  | a :: w, q => runWordAut trans w (trans a q)

/-- An automaton is **observable** (reduced) if no two distinct states have
identical future behavior. This is necessary for the factoring property. -/
def IsObservable {A O S Q : Type*} (aut : DetProofAutomaton A O S Q) : Prop :=
  ∀ q₁ q₂ : Q, (∀ (w : List A) (o : O),
    aut.output o (runWordAut aut.transition w q₁) =
    aut.output o (runWordAut aut.transition w q₂)) → q₁ = q₂




/-! ## §8. Residual Semimodule Structure -/

/-- The residual action of a contraction symbol on trace profiles. -/
def residualAction {A O S : Type*} (a : A) :
    (List A × O → S) → (List A × O → S) :=
  fun profile ⟨w, o⟩ => profile ⟨a :: w, o⟩




/-! ## §9. Trace Injectivity on Quotient -/


/-! ## §10. Ultrametric Geometry -/

/-- An ultrametric pseudo-distance function. -/
structure IsUltrametric {X : Type*} (d : X → X → ℝ) : Prop where
  dist_nonneg : ∀ x y, 0 ≤ d x y
  dist_self : ∀ x, d x x = 0
  dist_symm : ∀ x y, d x y = d y x
  dist_triangle : ∀ x y z, d x z ≤ max (d x y) (d y z)

/-
**Ultrametric isosceles theorem**: if two sides of a triangle differ,
the longest two are equal. All ultrametric triangles are isosceles.
Bridge: non-Archimedean geometry → hierarchical proof spaces.
-/


/-! ## §11. Observer-Induced Ultrametric -/

/-- Observer separation score: max absolute discrepancy over observers. -/
def obsSep {P O : Type*} [Fintype O] [Nonempty O]
    (obs : O → P → ℝ) (p q : P) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty
    (fun o => |obs o p - obs o q|)

/-
Observer separation is nonnegative.
-/

/-
Observer separation of a point with itself is zero.
-/

/-
Observer separation is symmetric.
-/

/-
Observer separation satisfies the (ordinary) triangle inequality.
Note: For general real-valued observers, the sup-metric is NOT ultrametric.
Ultrametricity holds when observers take values in a discrete set (e.g., Bool).
-/

/-
For {0,1}-valued (Boolean) observers, obsSep satisfies the ultrametric inequality.
This is because each |obs o p - obs o r| ∈ {0, 1}, and if p,r differ at observer o,
then either p,q or q,r must also differ at o (pigeonhole on Bool).
-/

/-! ## §12. Reconstruction Witness and Duality Theorem -/

/-- A reconstruction witness for the quotient automaton. -/
structure ReconstructionWitness (P : Type*) {A O S : Type*}
    (step : A → P → P) (obs : O → P → S) where
  quotientMap : P → StateQuotient P step obs
  surjective : Function.Surjective quotientMap
  step_compat : ∀ a p, quotientMap (step a p) = quotientStep step obs a (quotientMap p)
  obs_compat : ∀ o p, obs o p = quotientObs step obs o (quotientMap p)

/-- The canonical reconstruction witness. -/
def canonicalReconstruction {P A O S : Type*}
    (step : A → P → P) (obs : O → P → S) :
    ReconstructionWitness P step obs where
  quotientMap := fun p => @Quotient.mk _ (obsSetoid P step obs) p
  surjective := Quotient.exists_rep
  step_compat := fun _ _ => rfl
  obs_compat := fun _ _ => rfl


/-! ## §13. Fixed-Point Characterization -/

/-- A state is a fixed point of all contractions. -/
def IsFixedPoint {P A : Type*} (step : A → P → P) (p : P) : Prop :=
  ∀ a : A, step a p = p



/-! ## §14. Two-Observer Separation -/


/-! ## §15. Diagonal Stability -/


/-! ## §16. Residual Composition -/



/-! ## §17. Concrete Examples -/

/-! ## §18. Non-Expansiveness -/


/-! ## §19. Quotient Step Functoriality -/


/-! ## §20. Observer Count Lower Bound -/


end UltrametricProofAutomaton


