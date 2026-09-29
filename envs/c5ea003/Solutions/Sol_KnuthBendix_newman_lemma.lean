-- Prove2me | solution 1 for KnuthBendix.newman_lemma
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:53:40.719669+00:00
-- url     : https://prove2.me/submissions/c4f5684a-36f2-4bd4-accc-e553bcb0e79d

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
    (h_term : IsTerminating R)
    (h_local : IsLocallyConfluent R) :
    IsConfluent R := by
  have h_ind : ∀ t, (∀ s, R t s → ∀ u₁ u₂, ReflTransGen R s u₁ → ReflTransGen R s u₂ → ∃ v, ReflTransGen R u₁ v ∧ ReflTransGen R u₂ v) → ∀ u₁ u₂, ReflTransGen R t u₁ → ReflTransGen R t u₂ → ∃ v, ReflTransGen R u₁ v ∧ ReflTransGen R u₂ v := by
    intro t ht u₁ u₂ hu₁ hu₂
    by_cases h_cases : u₁ = t ∨ u₂ = t;
    · grind;
    · obtain ⟨s₁, hs₁⟩ : ∃ s₁, R t s₁ ∧ ReflTransGen R s₁ u₁ := by
        have h_nf_of_rtc : ∀ (t u : T), ReflTransGen R t u → t = u ∨ ∃ s, R t s ∧ ReflTransGen R s u := by
          intro t u htu
          induction' htu with t u htu ih;
          · exact Or.inl rfl;
          · grind;
        exact h_nf_of_rtc t u₁ hu₁ |> Or.rec ( fun h => False.elim ( h_cases <| Or.inl h.symm ) ) fun h => h
      obtain ⟨s₂, hs₂⟩ : ∃ s₂, R t s₂ ∧ ReflTransGen R s₂ u₂ := by
        have := hu₂.cases_head; aesop;
      obtain ⟨ w, hw₁, hw₂ ⟩ := h_local hs₁.1 hs₂.1;
      obtain ⟨v₁, hv₁⟩ : ∃ v₁, ReflTransGen R u₁ v₁ ∧ ReflTransGen R w v₁ := by
        exact ht s₁ hs₁.1 u₁ w hs₁.2 hw₁
      obtain ⟨v₂, hv₂⟩ : ∃ v₂, ReflTransGen R v₁ v₂ ∧ ReflTransGen R u₂ v₂ := by
        exact ht s₂ hs₂.1 v₁ u₂ ( hw₂.trans hv₁.2 ) hs₂.2
      use v₂;
      exact ⟨ hv₁.1.trans hv₂.1, hv₂.2 ⟩;
  intro t u₁ u₂ h₁ h₂;
  contrapose! h_ind;
  obtain ⟨t, ht⟩ : ∃ t, (∃ u₁ u₂, ReflTransGen R t u₁ ∧ ReflTransGen R t u₂ ∧ ∀ v, ReflTransGen R u₁ v → ¬ReflTransGen R u₂ v) ∧ ∀ s, R t s → ¬(∃ u₁ u₂, ReflTransGen R s u₁ ∧ ReflTransGen R s u₂ ∧ ∀ v, ReflTransGen R u₁ v → ¬ReflTransGen R u₂ v) := by
    have := h_term.has_min { t | ∃ u₁ u₂, ReflTransGen R t u₁ ∧ ReflTransGen R t u₂ ∧ ∀ v, ReflTransGen R u₁ v → ¬ReflTransGen R u₂ v } ⟨ t, u₁, u₂, h₁, h₂, h_ind ⟩;
    exact ⟨ this.choose, this.choose_spec.1, fun s hs hs' => this.choose_spec.2 s hs' hs ⟩;
  exact ⟨ t, fun s hs u₁ u₂ hu₁ hu₂ => Classical.not_not.1 fun h => ht.2 s hs ⟨ u₁, u₂, hu₁, hu₂, fun v hv₁ hv₂ => h ⟨ v, hv₁, hv₂ ⟩ ⟩, ht.1 ⟩
