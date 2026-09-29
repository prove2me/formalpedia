-- Prove2me | solution 1 for CategoricalCoherence.TensorExpr.coherence_of_confluent_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-16T21:16:46.863552+00:00
-- url     : https://prove2.me/submissions/ef3d038d-218e-4237-93ad-9327a35500ca

-- Sol generated from Bridges/PosetTheory/CategoricalCoherence.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_CategoricalCoherence

/-!
# Categorical Coherence from Confluent Rewriting

This file establishes that **categorical coherence is an instance of confluent
rewriting theory**. We define a syntactic language of tensor expressions,
oriented structural rewrite rules (associativity, left unit, right unit),
and prove that these rules yield unique right-associated unit-free normal forms.

The central insight is that Mac Lane's coherence theorem for monoidal categories
can be re-derived as a corollary of the confluence of a simple term rewriting
system. This opens the door to **algorithmic coherence theory**, where coherence
theorems are proved by normalization and critical-pair analysis rather than
ad hoc combinatorial arguments.

## Main Results

### Normalization (Strategy A: Direct Flattening)
* `reduces_to_normalForm` — Every tensor expression reduces to its canonical
  normal form `rightAssoc (flatten t)` via the structural rewrite rules
* `normalize_idempotent` — Normal forms are fixed points of normalization
* `normalForm_rightAssoc` — The output of `rightAssoc` is always in normal form

### Flatten Invariance
* `flatten_invariant_of_step` — Flattening is preserved by one rewrite step
* `flatten_invariant_of_multiStep` — Flattening is preserved by multi-step reduction
* `flatten_invariant_of_equivGen` — Equivalent expressions have equal flattened forms

### Confluence and Coherence (Strategy B: Via Catalog Bridge)
* `monoidal_confluent` — The monoidal rewrite system is confluent
* `coherence_of_confluent_general` — General theorem: confluence implies coherence
* `coherence_of_confluent` — **Main theorem**: structural equivalence implies joinability

### Normal Form Uniqueness
* `normal_form_unique` — Two equivalent normal forms are syntactically equal
* `normalize_eq_of_equiv` — Equivalent terms normalize to the same expression

### Algorithmic Coherence (Strategy C: Critical Pairs)
* `coherence_of_critical_pairs` — Critical-pair joinability + termination → coherence
* `monoidal_coherence_certificate` — Verified normalization certificate with soundness,
  completeness, and canonicity proofs

### Decidability
* `monoidal_equiv_decidable` — The word problem for monoidal structural equivalence
  is decidable

### Cross-Domain: Associahedron
* `all_same_leaves_joinable` — All tensor trees with the same leaf sequence are
  joinable, connecting rewriting to the Stasheff associahedron

### Cross-Domain: Symmetric Monoidal (Permutation Theory)
* `flatten_perm_of_symStep` — Symmetric rewrite steps preserve leaf order up to permutation
* `symmetric_equiv_implies_perm` — Symmetric monoidal equivalence implies leaf permutation

## Proof Architecture

**Strategy A (Direct Normalization)** is the workhorse: we define `flatten` and
`rightAssoc`, show every term reduces to its canonical form, and that `flatten`
is a complete invariant. This is the most concrete and computationally effective route.

**Strategy B (Catalog Bridge)** lifts confluence to coherence: we prove a general
theorem that any confluent rewrite system has the coherence property (equivalence
implies joinability), then instantiate it for our monoidal rewrite system.

**Strategy C (Critical Pairs)** shows that coherence can in principle be verified
by checking local overlap joinability plus termination, mirroring Knuth–Bendix
completion. We state the theorem and derive it from the confluence already established.

application keywords: categorical coherence, confluent rewriting, completion theory,
normal forms, monoidal categories, symmetric monoidal categories, critical pairs,
Knuth–Bendix, associahedron, operads, decidable word problem, algorithmic category theory,
structural equivalence, circuit canonicalization, categorical quantum mechanics
-/

universe u

open CategoricalCoherence

-- ============================================================================
-- Section 1: Tensor Expressions
-- ============================================================================


open TensorExpr

variable {Obj : Type u}

-- ============================================================================
-- Section 2: Flattening and Right-Association
-- ============================================================================




-- ============================================================================
-- Section 3: Simp Lemmas for rightAssoc
-- ============================================================================



-- ============================================================================
-- Section 4: Structural Rewrite Steps (Oriented Monoidal Laws)
-- ============================================================================


-- ============================================================================
-- Section 5: Abstract Rewriting Definitions
-- ============================================================================





-- ============================================================================
-- Section 6: General Coherence from Confluence
-- ============================================================================


-- ============================================================================
-- Section 7: Flatten is Invariant Under Monoidal Steps
-- ============================================================================




-- ============================================================================
-- Section 8: Multi-Step Congruence Lemmas
-- ============================================================================



-- ============================================================================
-- Section 9: Reduction of rightAssoc Concatenation
-- ============================================================================


-- ============================================================================
-- Section 10: Main Normalization Theorem
-- ============================================================================



-- ============================================================================
-- Section 11: Normal Form Property of rightAssoc Output
-- ============================================================================






-- ============================================================================
-- Section 12: Normal Form Uniqueness
-- ============================================================================




-- ============================================================================
-- Section 13: Confluence
-- ============================================================================


-- ============================================================================
-- Section 14: Main Coherence Theorem
-- ============================================================================


-- ============================================================================
-- Section 15: Coherence Certificate
-- ============================================================================




-- ============================================================================
-- Section 16: Decidable Word Problem
-- ============================================================================



-- ============================================================================
-- Section 17: Cross-Domain — Associahedron Connection
-- ============================================================================



-- ============================================================================
-- Section 18: Critical-Pair Based Coherence
-- ============================================================================



-- ============================================================================
-- Section 19: Symmetric Monoidal Extension
-- ============================================================================




-- ============================================================================
-- Section 20: Monoidal Rewrite Presentation Structure
-- ============================================================================



-- ============================================================================
-- Section 21: Verified Normalization Algorithm
-- ============================================================================





-- ============================================================================
-- Section 22: Normal Form Characterization Predicates
-- ============================================================================




-- ============================================================================
-- Section 23: Structural Joinability (Novel Definition)
-- ============================================================================



-- ============================================================================
-- Section 24: Conjecture Statement — Symmetric Coherence = Permutation
-- ============================================================================



open CategoricalCoherence in
theorem solution{α : Type*}
    (R : α → α → Prop)
    (hconfluent : IsConfluent R) :
    CoherentPresentation R := by
  intro a b hab
  induction hab with
  | rel x y hxy =>
    exact ⟨y, Relation.ReflTransGen.single hxy, Relation.ReflTransGen.refl⟩
  | refl x =>
    exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm x y _ ih =>
    obtain ⟨c, hc1, hc2⟩ := ih
    exact ⟨c, hc2, hc1⟩
  | trans x y z _ _ ihxy ihyz =>
    obtain ⟨c₁, hc₁a, hc₁b⟩ := ihxy
    obtain ⟨c₂, hc₂a, hc₂b⟩ := ihyz
    obtain ⟨d, hd1, hd2⟩ := hconfluent y c₁ c₂ hc₁b hc₂a
    exact ⟨d, hc₁a.trans hd1, hc₂b.trans hd2⟩
