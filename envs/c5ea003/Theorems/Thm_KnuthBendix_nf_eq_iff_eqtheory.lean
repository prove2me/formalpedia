-- Prove2me | Theorems.Thm_KnuthBendix_nf_eq_iff_eqtheory
-- name    : KnuthBendix.nf_eq_iff_eqtheory
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:50:16.309058+00:00
-- url     : https://prove2.me/theorems/b1cc0b43-fb24-4d73-afb7-34f27fb0925e
-- title:
--   Nf eq iff eqtheory
-- statement:
--   Formal statement of `KnuthBendix.nf_eq_iff_eqtheory` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem KnuthBendix.nf_eq_iff_eqtheory{T : Type*} {R : T → T → Prop}
--       (h_conv : IsConvergent R)
--       (nf : T → T)
--       (h_nf_nf : ∀ t, IsNF R (nf t))
--       (h_nf_red : ∀ t, ReflTransGen R t (nf t))
--       {s t : T} :
--       nf s = nf t ↔ EqTheory R s t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/KnuthBendixCompletion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/KnuthBendixCompletion.lean#L229

-- Thm stub generated from Bridges/PosetTheory/KnuthBendixCompletion.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_KnuthBendixCompletion

/-!
# Certified Knuth-Bendix Completion: Automated Synthesis of Convergent Rewrite Systems

## Overview

This file formalizes the core theory of Knuth-Bendix completion at the level of
abstract rewrite systems (ARS). We establish:

1. **Newman's Lemma**: Terminating + locally confluent ⟹ confluent
2. **Equational theory preservation**: KB completion steps preserve the equational theory
3. **Convergent completion theorem**: Terminated completion yields a convergent system
4. **Bridge to certified optimization**: Convergent systems yield semantics-preserving normalizers

These results close the loop from equational specifications to certified optimizers:
  equations → KB completion → convergence certificate → normalizer → optimizer

## Design

We work at the level of abstract rewrite systems, parameterized by a type `T` and
a step relation `R : T → T → Prop`. This separates the logical structure of
completion from syntactic details of first-order terms, enabling the theorems
to apply to any concrete term algebra.

## Lineage

Builds on `Pythagorean/ConvergentRewriteOptimizer.lean` conceptually:
- Extends the `CertifiedNormalizer` / `RewriteSound` architecture
- The completion pipeline composes with the existing optimizer architecture
-/

open Relation

open KnuthBendix

/-! ## Part 1: Abstract Rewrite System Properties -/









/-! ## Part 2: Newman's Lemma -/

/-
If `t` is in normal form and `t →* u`, then `t = u`.
-/

/-
**Newman's Lemma.** A terminating, locally confluent ARS is confluent.

This is the cornerstone of Knuth-Bendix completion. It reduces confluence
(a global property) to local confluence (checkable via critical pairs).

**Proof sketch.** Well-founded induction on `t` using termination.
Given `t →* u₁` and `t →* u₂`, if either path is trivial, done.
Otherwise `t → s₁ →* u₁` and `t → s₂ →* u₂`. Local confluence
gives a join of `s₁, s₂` at some `w`. Inductive hypothesis on `s₁`
(smaller than `t`) joins `w` and `u₁` at some `v₁`. Then inductive
hypothesis on `w` (reachable from `s₂`, smaller than `t`) joins `v₁`
with the path from `s₂` to `u₂`.
-/

/-
In a convergent system, normal forms are unique.
-/

/-
In a terminating system, every term has a normal form.
-/

/-
A convergent system has a unique normal form for each term.
-/

/-! ## Part 3: Multi-step Soundness -/

/-
Multi-step rewrite soundness: if single steps preserve evaluation,
    so does the reflexive-transitive closure.
-/

/-
The master optimizer theorem: a convergent sound rewrite system's normalizer
    preserves evaluation.
-/

/-! ## Part 4: Equational Theory -/



/-
The reflexive-transitive closure is contained in the equational theory.
-/

/-
In a convergent system, two terms have the same normal form iff they are
in the same equational theory class.
-/

theorem KnuthBendix.nf_eq_iff_eqtheory{T : Type*} {R : T → T → Prop}
    (h_conv : IsConvergent R)
    (nf : T → T)
    (h_nf_nf : ∀ t, IsNF R (nf t))
    (h_nf_red : ∀ t, ReflTransGen R t (nf t))
    {s t : T} :
    nf s = nf t ↔ EqTheory R s t := by sorry
