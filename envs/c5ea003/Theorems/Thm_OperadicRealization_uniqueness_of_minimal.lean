-- Prove2me | Theorems.Thm_OperadicRealization_uniqueness_of_minimal
-- name    : OperadicRealization.uniqueness_of_minimal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:59:08.570796+00:00
-- url     : https://prove2.me/theorems/14fa1a14-4cbd-4985-8408-49b2fe1c111a
-- title:
--   Uniqueness of minimal
-- statement:
--   Formal statement of `OperadicRealization.uniqueness_of_minimal` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem OperadicRealization.uniqueness_of_minimal    (A B : Architecture S G Obs)
--       {sem : ObsSem S G Obs}
--       (hA : Realizes A sem) (hB : Realizes B sem)
--       (hsepA : ObsSeparated A) (hsepB : ObsSeparated B)
--       (hreachA : Reachable A) (hreachB : Reachable B) :
--       ∃ f : A.alg.carrier → B.alg.carrier,
--         Bijective f ∧
--         (∀ t : Term S G, f (A.state t) = B.state t) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/OperadicRealizationDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/OperadicRealizationDuality.lean#L350

-- Thm stub generated from Bridges/OperadicRealizationDuality.lean
import Mathlib
import Definitions.Def_Bridges_OperadicRealizationDuality
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

open OperadicRealization

/-! ## §1. Signatures and Terms -/







/-! ## §2. Algebras and Architectures -/


variable {S : AlgSignature} {G Obs : Type}







/-! ## §3. Observable Semantics and Context Equivalence -/


def Architecture.toSem (A : Architecture S G Obs) : ObsSem S G Obs := A.behavior








/-! ## §4. Context Equivalence is a Congruence

The central algebraic theorem: if `tᵢ ~ uᵢ` for all i, then
`op(t₁,...,tₙ) ~ op(u₁,...,uₙ)`. -/



/-! ## §5. Architecture Morphisms -/




/-! ## §6. Realization and Core Theorems -/







/-! ## §7. Observable Separation and Full Abstraction -/




/-! ## §8. Minimality and Uniqueness -/

/-
**Minimality theorem.** The observably separated, reachable realization
    is surjected onto from any other realization.
-/

/-
**Uniqueness of minimal realizations.**
-/

theorem OperadicRealization.uniqueness_of_minimal    (A B : Architecture S G Obs)
    {sem : ObsSem S G Obs}
    (hA : Realizes A sem) (hB : Realizes B sem)
    (hsepA : ObsSeparated A) (hsepB : ObsSeparated B)
    (hreachA : Reachable A) (hreachB : Reachable B) :
    ∃ f : A.alg.carrier → B.alg.carrier,
      Bijective f ∧
      (∀ t : Term S G, f (A.state t) = B.state t) := by sorry
