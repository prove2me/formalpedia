-- Prove2me | Definitions.Def_Bridges_PosetTheory_CategoricalCoherence
-- name    : Bridges_PosetTheory_CategoricalCoherence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:27:37.070348+00:00
-- url     : https://prove2.me/theorems/c6277170-0061-43c8-8329-8288247df73f
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_CategoricalCoherence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.CategoricalCoherence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/CategoricalCoherence.lean by skeleton subtraction
import Mathlib

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

namespace CategoricalCoherence

-- ============================================================================
-- Section 1: Tensor Expressions
-- ============================================================================

/-- Syntactic tensor expressions over a type of objects.
    These represent the free monoidal syntax: variables, the monoidal unit,
    and binary tensor products. Before quotienting by structural isomorphisms,
    expressions form a free algebra. -/
inductive TensorExpr (Obj : Type u) where
  | var : Obj → TensorExpr Obj
  | unit : TensorExpr Obj
  | tensor : TensorExpr Obj → TensorExpr Obj → TensorExpr Obj
  deriving DecidableEq, Repr

namespace TensorExpr

variable {Obj : Type u}

-- ============================================================================
-- Section 2: Flattening and Right-Association
-- ============================================================================

/-- Flatten a tensor expression to a list of variables, erasing units
    and reading leaves left-to-right. This is the semantic content of
    a tensor expression modulo structural isomorphisms.

    The key property is that `flatten` is invariant under all structural
    rewrite rules, making it a complete invariant for the equivalence
    relation generated by the monoidal structural laws. -/
def flatten : TensorExpr Obj → List Obj
  | var x => [x]
  | unit => []
  | tensor a b => a.flatten ++ b.flatten

/-- Reconstruct a canonical right-associated tensor expression from a list
    of variables. The output is always in normal form:
    - `[]` maps to `unit`
    - `[x]` maps to `var x`
    - `x :: y :: ys` maps to `tensor (var x) (rightAssoc (y :: ys))` -/
def rightAssoc : List Obj → TensorExpr Obj
  | [] => unit
  | [x] => var x
  | x :: y :: ys => tensor (var x) (rightAssoc (y :: ys))

@[simp] theorem rightAssoc_cons_cons (x y : Obj) (ys : List Obj) :
    rightAssoc (x :: y :: ys) = (var x).tensor (rightAssoc (y :: ys)) := rfl

/-- The canonical normal form: flatten then right-associate. -/
def normalize (t : TensorExpr Obj) : TensorExpr Obj :=
  rightAssoc (flatten t)

-- ============================================================================
-- Section 3: Simp Lemmas for rightAssoc
-- ============================================================================


/-- **Lemma**: `flatten ∘ rightAssoc = id`. The flattening of a right-associated
    tree recovers the original list. This is the key roundtrip property. -/
@[simp] theorem flatten_rightAssoc (l : List Obj) : flatten (rightAssoc l) = l := by
  induction l with
  | nil => simp [flatten, rightAssoc]
  | cons x xs ih =>
    cases xs with
    | nil => simp [rightAssoc, flatten]
    | cons y ys => simp [rightAssoc, flatten, ih]

-- ============================================================================
-- Section 4: Structural Rewrite Steps (Oriented Monoidal Laws)
-- ============================================================================

/-- One-step structural rewriting for monoidal categories.
    These are the oriented structural isomorphisms:
    - **Associativity**: `(A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)` (re-bracket rightward)
    - **Left unit**: `I ⊗ A → A` (erase left unit)
    - **Right unit**: `A ⊗ I → A` (erase right unit)

    Plus congruence closure: if `a → a'` then `a ⊗ b → a' ⊗ b` and
    `b ⊗ a → b ⊗ a'`. This makes the rewrite system compatible with the
    tensor structure. -/
inductive MonoidalStep : TensorExpr Obj → TensorExpr Obj → Prop where
  | assoc (a b c : TensorExpr Obj) :
      MonoidalStep (tensor (tensor a b) c) (tensor a (tensor b c))
  | unitL (a : TensorExpr Obj) :
      MonoidalStep (tensor unit a) a
  | unitR (a : TensorExpr Obj) :
      MonoidalStep (tensor a unit) a
  | tensorL {a a' : TensorExpr Obj} (b : TensorExpr Obj) :
      MonoidalStep a a' → MonoidalStep (tensor a b) (tensor a' b)
  | tensorR (a : TensorExpr Obj) {b b' : TensorExpr Obj} :
      MonoidalStep b b' → MonoidalStep (tensor a b) (tensor a b')

-- ============================================================================
-- Section 5: Abstract Rewriting Definitions
-- ============================================================================

variable {α : Type*}

/-- Two terms are **joinable** if they reduce to a common term via
    zero or more rewrite steps. -/
def Joinable (R : α → α → Prop) (a b : α) : Prop :=
  ∃ c, Relation.ReflTransGen R a c ∧ Relation.ReflTransGen R b c

/-- A term is in **normal form** if no reduction step applies to it. -/
def IsNormalForm (R : α → α → Prop) (a : α) : Prop :=
  ∀ b, ¬ R a b

/-- A relation is **confluent** (Church-Rosser) if all divergent paths
    re-converge: whenever `a →* b` and `a →* c`, then `b` and `c` are
    joinable. -/
def IsConfluent (R : α → α → Prop) : Prop :=
  ∀ a b c, Relation.ReflTransGen R a b →
    Relation.ReflTransGen R a c → Joinable R b c

/-- A presentation is **coherent** if equivalence implies joinability.
    This is the rewriting-theoretic formulation of Mac Lane's coherence:
    any two parallel structural morphisms (= equivalent tensor expressions)
    reduce to a common canonical form. -/
def CoherentPresentation (R : α → α → Prop) : Prop :=
  ∀ a b, Relation.EqvGen R a b → Joinable R a b

-- ============================================================================
-- Section 6: General Coherence from Confluence
-- ============================================================================


-- ============================================================================
-- Section 7: Flatten is Invariant Under Monoidal Steps
-- ============================================================================

/-- **Key Lemma**: Flattening is preserved by one-step structural rewriting.
    Each structural rule preserves the list of variables:
    - Associativity: `(a ++ b) ++ c = a ++ (b ++ c)` (list associativity)
    - Left unit: `[] ++ a = a`
    - Right unit: `a ++ [] = a`
    - Congruence: induction on the position of the step -/
theorem flatten_invariant_of_step {a b : TensorExpr Obj}
    (h : MonoidalStep a b) : flatten a = flatten b := by
  induction h with
  | assoc a b c => simp [flatten, List.append_assoc]
  | unitL a => simp [flatten]
  | unitR a => simp [flatten]
  | tensorL b _ ih => simp [flatten, ih]
  | tensorR a _ ih => simp [flatten, ih]


/-- **Theorem**: Flatten is invariant under the equivalence generated by
    monoidal steps. Equivalent expressions have the same flattened form.
    This makes `flatten` a complete invariant for structural equivalence. -/
theorem flatten_invariant_of_equivGen {a b : TensorExpr Obj}
    (h : Relation.EqvGen MonoidalStep a b) : flatten a = flatten b := by
  induction h with
  | rel _ _ h => exact flatten_invariant_of_step h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

-- ============================================================================
-- Section 8: Multi-Step Congruence Lemmas
-- ============================================================================

/-- Lift multi-step reduction under right tensor position. -/
theorem multiStep_tensorR (a : TensorExpr Obj) {b b' : TensorExpr Obj}
    (h : Relation.ReflTransGen MonoidalStep b b') :
    Relation.ReflTransGen MonoidalStep (tensor a b) (tensor a b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih =>
    exact ih.trans (Relation.ReflTransGen.single (MonoidalStep.tensorR a h2))

/-- Lift multi-step reduction under left tensor position. -/
theorem multiStep_tensorL {a a' : TensorExpr Obj} (b : TensorExpr Obj)
    (h : Relation.ReflTransGen MonoidalStep a a') :
    Relation.ReflTransGen MonoidalStep (tensor a b) (tensor a' b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih =>
    exact ih.trans (Relation.ReflTransGen.single (MonoidalStep.tensorL b h2))

-- ============================================================================
-- Section 9: Reduction of rightAssoc Concatenation
-- ============================================================================

/-- **Lemma**: The tensor of two right-associated trees reduces to the
    right-associated tree of their concatenation.
    This is the key structural lemma that makes normalization work:
    it shows that `tensor (rightAssoc l₁) (rightAssoc l₂)` normalizes
    to `rightAssoc (l₁ ++ l₂)`. -/
theorem rightAssoc_append (l₁ l₂ : List Obj) :
    Relation.ReflTransGen MonoidalStep
      (tensor (rightAssoc l₁) (rightAssoc l₂))
      (rightAssoc (l₁ ++ l₂)) := by
  induction l₁ with
  | nil =>
    simp [rightAssoc]
    exact Relation.ReflTransGen.single (MonoidalStep.unitL _)
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [rightAssoc, List.cons_append, List.nil_append]
      cases l₂ with
      | nil =>
        simp [rightAssoc]
        exact Relation.ReflTransGen.single (MonoidalStep.unitR _)
      | cons y ys =>
        exact Relation.ReflTransGen.refl
    | cons y ys =>
      simp only [List.cons_append, rightAssoc_cons_cons]
      exact (Relation.ReflTransGen.single (MonoidalStep.assoc _ _ _)).trans
        (multiStep_tensorR (var x) ih)

-- ============================================================================
-- Section 10: Main Normalization Theorem
-- ============================================================================

/-- **Theorem (Reduction to Normal Form)**: Every tensor expression reduces
    to its canonical normal form `rightAssoc (flatten t)` via the structural
    rewrite rules.

    **Proof** by structural induction on tensor expressions:
    - `var x`: `normalize (var x) = var x` definitionally, so 0 steps.
    - `unit`: `normalize unit = unit` definitionally, so 0 steps.
    - `tensor a b`: First reduce `a` to `normalize a` and `b` to `normalize b`
      by the inductive hypotheses (under congruence). Then reduce
      `tensor (rightAssoc (flatten a)) (rightAssoc (flatten b))`
      to `rightAssoc (flatten a ++ flatten b)` by `rightAssoc_append`. -/
theorem reduces_to_normalForm (t : TensorExpr Obj) :
    Relation.ReflTransGen MonoidalStep t (normalize t) := by
  induction t with
  | var _ => exact Relation.ReflTransGen.refl
  | unit => exact Relation.ReflTransGen.refl
  | tensor a b ih_a ih_b =>
    simp only [normalize, flatten]
    exact ((multiStep_tensorL b ih_a).trans
      (multiStep_tensorR (normalize a) ih_b)).trans
      (rightAssoc_append _ _)

/-- **Theorem**: The normal form is idempotent — normalizing a normal form
    yields the same expression. -/
theorem normalize_idempotent (t : TensorExpr Obj) :
    normalize (normalize t) = normalize t := by
  simp [normalize, flatten_rightAssoc]

-- ============================================================================
-- Section 11: Normal Form Property of rightAssoc Output
-- ============================================================================






-- ============================================================================
-- Section 12: Normal Form Uniqueness
-- ============================================================================

/-- Two expressions with the same flatten normalize identically. -/
theorem normalize_eq_of_flatten_eq {a b : TensorExpr Obj}
    (h : flatten a = flatten b) : normalize a = normalize b := by
  simp [normalize, h]

/-- **Theorem**: Equivalent expressions have the same normal form. -/
theorem normalize_eq_of_equiv {a b : TensorExpr Obj}
    (h : Relation.EqvGen MonoidalStep a b) : normalize a = normalize b :=
  normalize_eq_of_flatten_eq (flatten_invariant_of_equivGen h)


-- ============================================================================
-- Section 13: Confluence
-- ============================================================================


-- ============================================================================
-- Section 14: Main Coherence Theorem
-- ============================================================================


-- ============================================================================
-- Section 15: Coherence Certificate
-- ============================================================================

/-- A **coherence certificate** bundles a normalization function with
    machine-checked proofs of soundness, completeness, and canonicity.
    This is a verified computational artifact: it constitutes a correct-by-
    construction decision procedure for structural equivalence. -/
structure CoherenceCertificate (Obj : Type u) where
  /-- The normalization function -/
  nf : TensorExpr Obj → TensorExpr Obj
  /-- **Soundness**: every term is equivalent to its normal form -/
  sound : ∀ t, Relation.EqvGen MonoidalStep t (nf t)
  /-- **Completeness**: terms with the same normal form are equivalent -/
  complete : ∀ a b, nf a = nf b → Relation.EqvGen MonoidalStep a b
  /-- **Canonicity**: the normal form function is idempotent -/
  canonical : ∀ t, nf (nf t) = nf t

/-- Helper: ReflTransGen implies EqvGen. -/
private theorem reflTransGen_to_eqvGen {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) : Relation.EqvGen R a b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hstep ih => exact ih.trans _ _ _ (Relation.EqvGen.rel _ _ hstep)

/-- **Verified Certificate**: The monoidal coherence certificate with
    machine-checked soundness, completeness, and canonicity. -/
noncomputable def monoidal_coherence_certificate : CoherenceCertificate Obj where
  nf := normalize
  sound := fun t => reflTransGen_to_eqvGen (reduces_to_normalForm t)
  complete := fun a b h => by
    have ha' := reflTransGen_to_eqvGen (reduces_to_normalForm a)
    have hb' := reflTransGen_to_eqvGen (reduces_to_normalForm b)
    exact ha'.trans _ _ _ (h ▸ (hb'.symm _ _))
  canonical := normalize_idempotent

-- ============================================================================
-- Section 16: Decidable Word Problem
-- ============================================================================

/-- **Theorem**: The word problem for monoidal structural equivalence is
    decidable. Two tensor expressions are equivalent iff their normal forms
    agree, and normal form equality is decidable when the object type has
    decidable equality.

    This gives a verified decision procedure for structural equivalence
    in monoidal categories. -/
instance monoidal_equiv_decidable [DecidableEq Obj] (a b : TensorExpr Obj) :
    Decidable (Relation.EqvGen MonoidalStep a b) := by
  by_cases h : normalize a = normalize b
  · exact isTrue (monoidal_coherence_certificate.complete a b h)
  · exact isFalse (fun heq => h (normalize_eq_of_equiv heq))


-- ============================================================================
-- Section 17: Cross-Domain — Associahedron Connection
-- ============================================================================

/-- Two tensor expressions have the **same leaf order** if they flatten to
    the same list. Combinatorially, this means they are vertices of the same
    **Stasheff associahedron**: different parenthesizations of the same
    sequence of variables. -/
def SameLeafOrder (a b : TensorExpr Obj) : Prop :=
  flatten a = flatten b


-- ============================================================================
-- Section 18: Critical-Pair Based Coherence
-- ============================================================================

/-- All local peaks of a relation are joinable (local confluence). -/
def AllLocalPeaksJoinable (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → Joinable R b c


-- ============================================================================
-- Section 19: Symmetric Monoidal Extension
-- ============================================================================

/-- Extended one-step rewriting for **symmetric** monoidal categories.
    Adds a braiding (swap) rule: `A ⊗ B → B ⊗ A`.

    Note: the symmetric system is NOT confluent (swapping is not oriented),
    but `flatten` still yields a permutation invariant. -/
inductive SymMonoidalStep : TensorExpr Obj → TensorExpr Obj → Prop where
  | assoc (a b c : TensorExpr Obj) :
      SymMonoidalStep (tensor (tensor a b) c) (tensor a (tensor b c))
  | unitL (a : TensorExpr Obj) :
      SymMonoidalStep (tensor unit a) a
  | unitR (a : TensorExpr Obj) :
      SymMonoidalStep (tensor a unit) a
  | swap (a b : TensorExpr Obj) :
      SymMonoidalStep (tensor a b) (tensor b a)
  | tensorL {a a' : TensorExpr Obj} (b : TensorExpr Obj) :
      SymMonoidalStep a a' → SymMonoidalStep (tensor a b) (tensor a' b)
  | tensorR (a : TensorExpr Obj) {b b' : TensorExpr Obj} :
      SymMonoidalStep b b' → SymMonoidalStep (tensor a b) (tensor a b')



-- ============================================================================
-- Section 20: Monoidal Rewrite Presentation Structure
-- ============================================================================



-- ============================================================================
-- Section 21: Verified Normalization Algorithm
-- ============================================================================

/-- The verified normalization algorithm for monoidal tensor expressions.
    Computes `rightAssoc (flatten t)`, which is the unique canonical
    right-associated unit-free representative of the equivalence class. -/
def normalizeMonoidal : TensorExpr Obj → TensorExpr Obj := normalize




-- ============================================================================
-- Section 22: Normal Form Characterization Predicates
-- ============================================================================




-- ============================================================================
-- Section 23: Structural Joinability (Novel Definition)
-- ============================================================================

/-- **Structural joinability** specializes joinability to structural rewrite
    systems. Two terms are structurally joinable if they share a common
    structural normal form reachable by oriented structural laws. -/
def StructuralJoinable (a b : TensorExpr Obj) : Prop :=
  Joinable MonoidalStep a b


-- ============================================================================
-- Section 24: Conjecture Statement — Symmetric Coherence = Permutation
-- ============================================================================


end TensorExpr
end CategoricalCoherence


