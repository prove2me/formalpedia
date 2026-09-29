-- Prove2me | Definitions.Def_Bridges_ClosureExtractorDuality
-- name    : Bridges_ClosureExtractorDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:53.074946+00:00
-- url     : https://prove2.me/theorems/2a9a6500-e071-4766-a87f-6bb692ea9cda
-- title:
--   Aether Catalog definitions — Bridges_ClosureExtractorDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureExtractorDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureExtractorDuality.lean by skeleton subtraction
import Mathlib
/-
# Closure–Extractor Duality

## Semantic Dictionary
- **Closed sets** ↔ entropy carriers (subsets with maximal dependency structure)
- **Closure-stable functionals** ↔ seed tests (predicates respecting dependency equivalence)
- **Evaluation matrix rows** ↔ extractor coordinates (binary encoding of functional evaluations)
- **Rank defect** ↔ entropy loss (gap between functional count and separation capacity)
- **Reconstruction** ↔ certified seed synthesis from matrix factorization data

## Overview
We formalize a finite duality between closure-generated dependency structures and
seeded extractor families. The main results:

1. **Closure invariance of deficiency**: The deficiency `|cl(A)| - |A|` depends only on
   the closure of A, not on A itself (for closed sets).
2. **Encoding–separation equivalence**: A family of closure-stable predicates separates
   elements in large closed sets iff the induced encoding map is injective on those sets.
3. **Main duality theorem**: Existence of a seed-indexed separating family ↔ existence of
   a closure-stable functional family with bounded rank defect.
4. **Certified reconstruction**: From a separating evaluation matrix, one can explicitly
   construct a seed family with certified entropy-loss bounds.
-/


open Finset Function

set_option linter.unusedSectionVars false

/-! ## §1. Closure Operators on Finite Types -/

/-- A closure operator on `Finset X` satisfying extensivity, monotonicity, and idempotence. -/
structure FinsetClosureOp (X : Type*) [DecidableEq X] where
  cl : Finset X → Finset X
  extensive : ∀ A : Finset X, A ⊆ cl A
  monotone : ∀ {A B : Finset X}, A ⊆ B → cl A ⊆ cl B
  idempotent : ∀ A : Finset X, cl (cl A) = cl A

variable {X : Type*} [DecidableEq X] [Fintype X]

namespace FinsetClosureOp

/-- A set is closed if it is a fixed point of the closure operator. -/
def IsClosed (op : FinsetClosureOp X) (C : Finset X) : Prop :=
  op.cl C = C

instance (op : FinsetClosureOp X) : DecidablePred op.IsClosed :=
  fun C => decEq (op.cl C) C


/-- Deficiency of a set A: `|cl(A)| - |A|`. -/
def deficiency (op : FinsetClosureOp X) (A : Finset X) : ℕ :=
  (op.cl A).card - A.card

/-- Entropy surrogate: `|X| - deficiency(A)`. -/
def entropySurrogate (op : FinsetClosureOp X) (A : Finset X) : ℕ :=
  Fintype.card X - op.deficiency A



end FinsetClosureOp

/-! ## §2. Closure-Stable Predicates and Functionals -/

/-- Two elements are closure-equivalent if their singleton closures are equal. -/
def closureEquiv (op : FinsetClosureOp X) (x y : X) : Prop :=
  op.cl {x} = op.cl {y}

/-- A closure-stable predicate: a Boolean predicate on elements of X that is
    constant on closure-equivalence classes. These are the "seed tests" in the
    cryptographic dictionary. -/
structure ClosureStablePred (op : FinsetClosureOp X) where
  test : X → Bool
  stable : ∀ x y : X, closureEquiv op x y → test x = test y

/-- The encoding map induced by a family of closure-stable predicates.
    Maps each element to its vector of predicate values. -/
def predicateEncoding {n : ℕ} (op : FinsetClosureOp X)
    (Φ : Fin n → ClosureStablePred op) (x : X) : Fin n → Bool :=
  fun i => (Φ i).test x

/-! ## §3. Separation Definitions -/

/-- A family of closure-stable predicates *k-separates* if for every closed set C
    with |C| ≥ k, and every pair of distinct elements in C, some predicate
    distinguishes them. -/
def PredicateFamilySeparates (op : FinsetClosureOp X) {n : ℕ}
    (Φ : Fin n → ClosureStablePred op) (k : ℕ) : Prop :=
  ∀ C : Finset X, op.IsClosed C → k ≤ C.card →
    ∀ x y : X, x ∈ C → y ∈ C → x ≠ y →
      ∃ i : Fin n, (Φ i).test x ≠ (Φ i).test y

/-- A seed-indexed family of maps *k-separates on closed sets* if for every closed set C
    with |C| ≥ k, and every pair of distinct elements in C, some seed gives different
    outputs. -/
def SeedFamilySeparates (op : FinsetClosureOp X) {Y Seed : Type*}
    [DecidableEq Y]
    (f : Seed → X → Y) (k : ℕ) : Prop :=
  ∀ C : Finset X, op.IsClosed C → k ≤ C.card →
    ∀ x y : X, x ∈ C → y ∈ C → x ≠ y →
      ∃ s : Seed, f s x ≠ f s y

/-- A seed-indexed family is *closure-compatible* if elements with the same
    singleton closure always receive the same output for each seed. -/
def ClosureCompatible (op : FinsetClosureOp X) {Y Seed : Type*}
    (f : Seed → X → Y) : Prop :=
  ∀ (s : Seed) (x y : X), closureEquiv op x y → f s x = f s y

/-! ## §4. Entropy Loss and Rank Defect -/


/-! ## §5. Evaluation Matrix -/

/-- A matrix k-separates closed sets if for each large closed set, distinct
    elements produce distinct column vectors. -/
def MatrixSeparatesClosedSets (op : FinsetClosureOp X) {n : ℕ}
    (M : Fin n → X → Bool) (k : ℕ) : Prop :=
  ∀ C : Finset X, op.IsClosed C → k ≤ C.card →
    ∀ x y : X, x ∈ C → y ∈ C → x ≠ y →
      ∃ i : Fin n, M i x ≠ M i y

/-! ## §6. Core Theorems -/


/-
**Backward Direction**: A family of closure-stable predicates that k-separates
    gives rise to a seed family that k-separates on closed sets.
    Construction: use a single "seed" and set `f () x := predicateEncoding Φ x`.
-/

/-
**Forward Direction**: A closure-compatible seed family that k-separates gives rise
    to closure-stable predicates that k-separate.

    Construction: for each `(s, y)` pair define `φ(x) := (f s x == y)`.
    Closure-compatibility ensures stability.
-/

/-
**Certified Reconstruction**: From a Boolean matrix that separates large closed sets,
    construct an explicit seed family achieving the same separation. The seed family
    maps each element to its column vector in the matrix.
-/

/-! ## §7. The Full Duality Theorem -/

/-
**Closure–Extractor Duality (Closed-Set Form)**.

    A finite-type duality between closure-stable predicate families and seed-indexed
    map families for separation on large closed sets.

    Direction 1 (predicates → seeds): Given predicates that separate, encoding yields
    a seed family that separates.

    This is the central bridge theorem connecting:
    - EML closure semantics (closed sets as dependency carriers)
    - Idempotent algebra (Boolean predicates as the simplest idempotent-semiring functionals)
    - Cryptographic extraction (seed families as seeded extractors)
    - Certified reconstruction (encoding map as explicit algorithm)
-/


/-
**Matrix–Seed reconstruction bridge**: a separating matrix directly gives a
    separating seed family, completing the certified reconstruction pipeline.
-/


