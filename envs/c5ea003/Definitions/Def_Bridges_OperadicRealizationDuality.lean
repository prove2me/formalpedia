-- Prove2me | Definitions.Def_Bridges_OperadicRealizationDuality
-- name    : Bridges_OperadicRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:53.984162+00:00
-- url     : https://prove2.me/theorems/bbf4908f-3eb9-4418-a286-78874b5ed5c1
-- title:
--   Aether Catalog definitions — Bridges_OperadicRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.OperadicRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/OperadicRealizationDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Operadic Realization–Minimality Duality via Context Equivalence

This file formalizes a Myhill–Nerode style minimization theorem for algebraic
architectures with observable semantics, bridging universal algebra, machine
learning architecture minimization, proof-circuit semantics, and weighted
automata realization theory.

## Main Results

* `ctxEquiv_isEquivalence` — context equivalence is an equivalence relation
* `ctxEquiv_congruence` — context equivalence is a congruence (preserved by ops)
* `state_factors_ctxEquiv` — state equiv refines context equiv (forward Myhill–Nerode)
* `separated_stateEquiv_iff_ctxEquiv` — full abstraction for separated architectures
* `morphism_preserves_behavior` — arch morphisms preserve observable behavior
* `minimality_via_separation` — separated reachable realization is minimal
* `uniqueness_of_minimal` — minimal realizations are isomorphic

## Mathematical Overview

Given a signature and observable semantics mapping terms to observations,
context equivalence identifies terms indistinguishable in all one-hole contexts.
We prove this is the coarsest congruence compatible with observations, yielding
a canonical minimal architecture via quotient — the algebraic generalization of
the Myhill–Nerode theorem to operadic/many-input structures.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Function Set

noncomputable section

namespace OperadicRealization

/-! ## §1. Signatures and Terms -/

/-- An algebraic signature: operation symbols with arities. -/
structure AlgSignature where
  Op : Type
  arity : Op → ℕ

/-- Terms over a signature with generators from `G`. -/
inductive Term (S : AlgSignature) (G : Type) : Type where
  | gen : G → Term S G
  | app : (op : S.Op) → (Fin (S.arity op) → Term S G) → Term S G

/-- One-hole contexts for substitution. -/
inductive Ctx (S : AlgSignature) (G : Type) : Type where
  | hole : Ctx S G
  | app : (op : S.Op) → (focus : Fin (S.arity op)) →
          (others : Fin (S.arity op) → Term S G) →
          (sub : Ctx S G) → Ctx S G

/-- Plug a term into a context's hole. -/
def Ctx.plug {S : AlgSignature} {G : Type} : Ctx S G → Term S G → Term S G
  | .hole, t => t
  | .app op focus others sub, t =>
    .app op (fun j => if j = focus then sub.plug t else others j)

/-- Compose two contexts. -/
def Ctx.comp {S : AlgSignature} {G : Type} :
    Ctx S G → Ctx S G → Ctx S G
  | .hole, c₂ => c₂
  | .app op focus others sub, c₂ => .app op focus others (sub.comp c₂)


/-! ## §2. Algebras and Architectures -/

/-- An algebra over a signature. -/
structure SigAlgebra (S : AlgSignature) where
  carrier : Type
  interpOp : (op : S.Op) → (Fin (S.arity op) → carrier) → carrier

variable {S : AlgSignature} {G Obs : Type}

/-- Evaluate a term in an algebra. -/
def SigAlgebra.eval (A : SigAlgebra S) (assign : G → A.carrier) :
    Term S G → A.carrier
  | .gen g => assign g
  | .app op args => A.interpOp op (fun i => A.eval assign (args i))

/-- Evaluate a context with a hole value. -/
def SigAlgebra.evalCtx (A : SigAlgebra S) (assign : G → A.carrier) :
    Ctx S G → A.carrier → A.carrier
  | .hole, v => v
  | .app op focus others sub, v =>
    A.interpOp op (fun j =>
      if j = focus then A.evalCtx assign sub v
      else A.eval assign (others j))


/-- A finite architecture: algebra + generators + observations. -/
structure Architecture (S : AlgSignature) (G Obs : Type) where
  alg : SigAlgebra S
  init : G → alg.carrier
  observe : alg.carrier → Obs

@[simp] def Architecture.state (A : Architecture S G Obs) (t : Term S G) :
    A.alg.carrier := A.alg.eval A.init t

def Architecture.behavior (A : Architecture S G Obs) (t : Term S G) : Obs :=
  A.observe (A.state t)

/-! ## §3. Observable Semantics and Context Equivalence -/

abbrev ObsSem (S : AlgSignature) (G Obs : Type) := Term S G → Obs

def Architecture.toSem (A : Architecture S G Obs) : ObsSem S G Obs := A.behavior

/-- **Context equivalence:** two terms are equivalent iff indistinguishable
    in all one-hole contexts. -/
def ctxEquiv (sem : ObsSem S G Obs) (t u : Term S G) : Prop :=
  ∀ c : Ctx S G, sem (c.plug t) = sem (c.plug u)

theorem ctxEquiv_refl (sem : ObsSem S G Obs) (t : Term S G) :
    ctxEquiv sem t t := fun _ => rfl

theorem ctxEquiv_symm {sem : ObsSem S G Obs} {t u : Term S G}
    (h : ctxEquiv sem t u) : ctxEquiv sem u t :=
  fun c => (h c).symm

theorem ctxEquiv_trans {sem : ObsSem S G Obs} {t u v : Term S G}
    (h1 : ctxEquiv sem t u) (h2 : ctxEquiv sem u v) :
    ctxEquiv sem t v :=
  fun c => (h1 c).trans (h2 c)

/-- Context equivalence is an equivalence relation. -/
theorem ctxEquiv_isEquivalence (sem : ObsSem S G Obs) :
    Equivalence (ctxEquiv sem) :=
  ⟨ctxEquiv_refl sem, fun h => ctxEquiv_symm h, fun h1 h2 => ctxEquiv_trans h1 h2⟩

def ctxSetoid (sem : ObsSem S G Obs) : Setoid (Term S G) :=
  ⟨ctxEquiv sem, ctxEquiv_isEquivalence sem⟩

/-- Context equivalence at the hole gives semantic equality. -/
theorem ctxEquiv_implies_sem_eq {sem : ObsSem S G Obs}
    {t u : Term S G} (h : ctxEquiv sem t u) :
    sem t = sem u := h Ctx.hole

/-! ## §4. Context Equivalence is a Congruence

The central algebraic theorem: if `tᵢ ~ uᵢ` for all i, then
`op(t₁,...,tₙ) ~ op(u₁,...,uₙ)`. -/



/-! ## §5. Architecture Morphisms -/

structure ArchMorphism (A B : Architecture S G Obs) where
  toFun : A.alg.carrier → B.alg.carrier
  map_op : ∀ (op : S.Op) (args : Fin (S.arity op) → A.alg.carrier),
    toFun (A.alg.interpOp op args) = B.alg.interpOp op (fun i => toFun (args i))
  map_init : ∀ g : G, toFun (A.init g) = B.init g
  map_obs : ∀ s : A.alg.carrier, A.observe s = B.observe (toFun s)



/-! ## §6. Realization and Core Theorems -/

def Realizes (A : Architecture S G Obs) (sem : ObsSem S G Obs) : Prop :=
  ∀ t : Term S G, A.behavior t = sem t






/-! ## §7. Observable Separation and Full Abstraction -/

/-- An architecture is observably separated if distinct states yield
    different observations in some context. -/
def ObsSeparated (A : Architecture S G Obs) : Prop :=
  ∀ s₁ s₂ : A.alg.carrier,
    (∀ c : Ctx S G, A.observe (A.alg.evalCtx A.init c s₁) =
                     A.observe (A.alg.evalCtx A.init c s₂)) →
    s₁ = s₂

def Reachable (A : Architecture S G Obs) : Prop :=
  Surjective (fun t : Term S G => A.state t)


/-! ## §8. Minimality and Uniqueness -/

/-
**Minimality theorem.** The observably separated, reachable realization
    is surjected onto from any other realization.
-/

/-
**Uniqueness of minimal realizations.**
-/

/-! ## §9. Concrete Instance -/

def UnarySig : AlgSignature where
  Op := Unit; arity := fun _ => 1

def boolUnaryArch : Architecture UnarySig (Fin 2) Bool where
  alg := {
    carrier := Bool
    interpOp := fun _ args => !args ⟨0, by simp [UnarySig]⟩
  }
  init := fun i => i = 0
  observe := id



/-! ## §10. Quotient Algebra -/

def TermQuotient (sem : ObsSem S G Obs) := Quotient (ctxSetoid sem)

theorem obs_descends (sem : ObsSem S G Obs) :
    ∀ t u : Term S G, ctxEquiv sem t u → sem t = sem u :=
  fun _ _ h => ctxEquiv_implies_sem_eq h

def quotientObs (sem : ObsSem S G Obs) : TermQuotient sem → Obs :=
  Quotient.lift sem (obs_descends sem)


/-! ## §11. Realization Duality Bridge -/


/-! ## §12. Abstract Kernel Theory -/

def obsStateEquiv {State Obs' : Type} (observe : State → Obs') (s₁ s₂ : State) : Prop :=
  observe s₁ = observe s₂



end OperadicRealization


