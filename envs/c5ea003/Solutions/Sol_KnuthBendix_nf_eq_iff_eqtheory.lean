-- Prove2me | solution 1 for KnuthBendix.nf_eq_iff_eqtheory
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:53:41.199162+00:00
-- url     : https://prove2.me/submissions/ee1e0cc2-cc7a-401d-b80c-2690913e52c3

-- Sol generated from Bridges/PosetTheory/KnuthBendixCompletion.lean
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
theorem nf_of_rtc {T : Type*} {R : T → T → Prop} {t u : T}
    (hnf : IsNF R t) (h : ReflTransGen R t u) : t = u := by
  -- By induction on the length of the path from `t` to `u`.
  induction' h with u hu ih;
  · rfl;
  · exact False.elim ( hnf _ ( by subst_vars; assumption ) )

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
theorem unique_nf {T : Type*} {R : T → T → Prop}
    (h_conv : IsConvergent R)
    {t u₁ u₂ : T}
    (hn₁ : IsNF R u₁) (hn₂ : IsNF R u₂)
    (h₁ : ReflTransGen R t u₁) (h₂ : ReflTransGen R t u₂) :
    u₁ = u₂ := by
  -- By the confluence property, there exists a common reduct `v` such that `u₁ →* v` and `u₂ →* v`.
  obtain ⟨v, hv₁, hv₂⟩ : ∃ v, ReflTransGen R u₁ v ∧ ReflTransGen R u₂ v := by
    exact h_conv.2 h₁ h₂;
  -- By the uniqueness of normal forms, since `u₁` and `u₂` are both in normal form and reduce to `v`, they must be equal.
  have h_unique : u₁ = v := by
    exact?
  have h_unique' : u₂ = v := by
    exact?
  rw [h_unique, h_unique']

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
theorem rtc_sub_eqtheory {T : Type*} {R : T → T → Prop} {a b : T}
    (h : ReflTransGen R a b) : EqTheory R a b := by
  induction h;
  · exact EqvGen.refl _;
  · exact EqvGen.trans _ _ _ ‹_› ( EqvGen.rel _ _ ‹_› )

/-
In a convergent system, two terms have the same normal form iff they are
in the same equational theory class.
-/

/-! ## Part 5: Completion State and Steps -/






/-! ## Part 6: Completion Correctness -/

/-
**A sequence of KB steps preserves the equational theory.**
-/

/-
When completion finishes, the rules' equational theory equals
    the finished state's theory (since pending is empty).
-/

/-
**The Capstone Theorem: Terminated KB completion yields a convergent system.**

If completion runs from `S₀` to `S_final` where:
- Each step preserves the equational theory
- The final state has no pending equations
- The final rules are terminating
- The final rules are locally confluent (all critical pairs joined)

Then the final system is convergent and has the same equational theory.
-/

/-! ## Part 7: Bridge to Certified Optimizer -/


/-
**KB completion composes with certified optimization.**

The full pipeline: equations → completion → convergent system → normalizer → optimizer.
-/

/-
The normalizer is idempotent.
-/

/-
Two terms with the same normal form evaluate identically.
-/

/-! ## Part 8: Concrete Example — Boolean Ring Rewriting -/




/-
The idempotency rewrite is sound in `ZMod 2`.
-/


/-
The involution rewrite is sound in `ZMod 2`.
-/


open KnuthBendix in
theorem solution{T : Type*} {R : T → T → Prop}
    (h_conv : IsConvergent R)
    (nf : T → T)
    (h_nf_nf : ∀ t, IsNF R (nf t))
    (h_nf_red : ∀ t, ReflTransGen R t (nf t))
    {s t : T} :
    nf s = nf t ↔ EqTheory R s t := by
  constructor;
  · intro h_eq_nf
    have h_eq_nf_s : EqTheory R s (nf s) := by
      exact rtc_sub_eqtheory ( h_nf_red s )
    have h_eq_nf_t : EqTheory R t (nf t) := by
      exact rtc_sub_eqtheory ( h_nf_red t )
    rw [h_eq_nf] at h_eq_nf_s
    exact (by
    exact EqvGen.trans _ _ _ h_eq_nf_s ( EqvGen.symm _ _ h_eq_nf_t ));
  · intro h;
    apply unique_nf h_conv (h_nf_nf s) (h_nf_nf t) (h_nf_red s);
    induction h;
    · exact ReflTransGen.trans ( ReflTransGen.single ‹_› ) ( h_nf_red _ );
    · exact h_nf_red _;
    · grind +suggestions;
    · grind +suggestions
