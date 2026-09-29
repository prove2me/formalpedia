-- Prove2me | Definitions.Def_Tropical_NeuralCoding_EventGraphSemantics
-- name    : Tropical_NeuralCoding_EventGraphSemantics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:05.753868+00:00
-- url     : https://prove2.me/theorems/5e316c0a-c912-449b-8225-8a1878a37135
-- title:
--   Aether Catalog definitions — Tropical_NeuralCoding_EventGraphSemantics
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.NeuralCoding.EventGraphSemantics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/NeuralCoding/EventGraphSemantics.lean by skeleton subtraction
import Mathlib
/-
# Compositional Tropical Semantics for Event Graphs

This file formalizes a compositional theory of timed event-graph systems
using max-plus (tropical) matrix algebra. The key results are:

1. **Series composition** of event graphs corresponds to tropical matrix
   multiplication (max-plus matrix product).
2. **Parallel composition** with disjoint interfaces corresponds to tropical
   block-diagonal matrix sum.
3. **Parallel composition** with shared interfaces corresponds to pointwise
   tropical maximum.
4. **Throughput/cycle-time bounds** compose modularly: series adds bounds,
   parallel takes the max.

## Mathematical Framework

We work with event graphs whose transfer semantics are captured by matrices
over `ℝ`. The tropical semiring operations are:
- Tropical addition: `max`
- Tropical multiplication: `+` (classical addition)

The transfer matrix `M(G)_{i,k}` of an event graph `G` with input interface `ι`
and output interface `κ` records the maximum-weight path from each input to
each output, representing the longest delay / critical path timing.

## Key Definitions

- `tropMaxPlus A B`: max-plus matrix multiplication
- `EventGraph ι κ`: event graph with typed interfaces
- `transfer G`: the transfer matrix of `G`
- `series G₁ G₂`: series composition
- `parallel G₁ G₂`: parallel (disjoint) composition
- `parallelShared G₁ G₂`: parallel (shared-interface) composition
- `CycleTimeBound G c`: predicate asserting cycle-time ≤ c
-/

open Matrix Finset

noncomputable section

namespace TropicalEventGraph

/-! ## Max-Plus Matrix Operations -/

/-- Max-plus (tropical) matrix multiplication.
    `(A ⊗ B)_{i,k} = max_j (A_{i,j} + B_{j,k})`.
    This is the fundamental operation connecting series composition
    of event graphs to algebraic matrix operations. -/
def tropMaxPlus {ι κ μ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ) : Matrix ι μ ℝ :=
  fun i k => Finset.univ.sup' Finset.univ_nonempty (fun j => A i j + B j k)

/-- Tropical block-diagonal matrix: places `A` and `B` on diagonal blocks
    with `0` off-diagonal entries. -/
def tropBlockDiag {α₁ β₁ α₂ β₂ : Type}
    (A : Matrix α₁ β₁ ℝ) (B : Matrix α₂ β₂ ℝ) : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) ℝ :=
  fun i k => match i, k with
    | .inl a, .inl b => A a b
    | .inr a, .inr b => B a b
    | _, _ => 0

/-- Tropical pointwise maximum (tropical addition of matrices).
    Used for shared-interface parallel composition. -/
def tropPointwiseMax {ι κ : Type}
    (A B : Matrix ι κ ℝ) : Matrix ι κ ℝ :=
  fun i k => max (A i k) (B i k)

/-! ## Event Graph Structure -/

/-- An event graph with input interface `ι` and output interface `κ`.
    The transfer matrix records the maximum-weight (longest/critical) path
    from each input to each output.

    This is a "black-box" representation: we abstract away the internal
    structure and retain only the input-output transfer behavior. -/
structure EventGraph (ι κ : Type) where
  /-- The transfer matrix: `mat i k` is the max-weight path from input `i`
      to output `k`. -/
  mat : Matrix ι κ ℝ

/-! ## Transfer Semantics -/

/-- Extract the transfer matrix from an event graph. -/
def transfer {ι κ : Type} (G : EventGraph ι κ) : Matrix ι κ ℝ := G.mat

/-! ## Composition Operations -/

/-- Series composition: connect output of `G₁` to input of `G₂`.
    The resulting transfer matrix is the max-plus product of the two
    transfer matrices. -/
def series {ι κ μ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (G₁ : EventGraph ι κ) (G₂ : EventGraph κ μ) : EventGraph ι μ :=
  ⟨tropMaxPlus G₁.mat G₂.mat⟩

/-- Parallel composition with disjoint interfaces. -/
def parallel {α₁ β₁ α₂ β₂ : Type}
    (G₁ : EventGraph α₁ β₁) (G₂ : EventGraph α₂ β₂) : EventGraph (α₁ ⊕ α₂) (β₁ ⊕ β₂) :=
  ⟨tropBlockDiag G₁.mat G₂.mat⟩

/-- Parallel composition with shared interfaces. -/
def parallelShared {ι κ : Type}
    (G₁ G₂ : EventGraph ι κ) : EventGraph ι κ :=
  ⟨tropPointwiseMax G₁.mat G₂.mat⟩

/-! ## Theorem 1: Series Composition = Tropical Matrix Multiplication -/


/-! ## Theorem 2a: Parallel (Disjoint) = Block Diagonal -/


/-! ## Theorem 2b: Parallel (Shared) = Pointwise Max -/


/-! ## Cycle-Time Bounds -/

/-- A cycle-time bound asserts that every entry of the transfer matrix
    is at most `c`. This captures that no critical path exceeds `c`. -/
def CycleTimeBound {ι κ : Type} (G : EventGraph ι κ) (c : ℝ) : Prop :=
  ∀ i k, G.mat i k ≤ c

/-! ## Theorem 3a: Series Throughput Certification -/

/-
**Series throughput theorem**: If `G₁` has cycle-time bound `c₁` and
    `G₂` has cycle-time bound `c₂`, then their series composition has
    cycle-time bound `c₁ + c₂`.
-/

/-! ## Theorem 3b: Parallel (Disjoint) Throughput Certification -/

/-
**Parallel throughput theorem (disjoint)**: Cycle-time bound is max.
    Requires `0 ≤ c₁` and `0 ≤ c₂` because off-diagonal (cross-system)
    entries are `0`, representing the absence of paths.
-/

/-! ## Theorem 3c: Shared-Parallel Throughput Certification -/

/-
**Shared-parallel throughput theorem**: Cycle-time bound is max.
-/

/-! ## Associativity of Max-Plus Matrix Multiplication -/

/-
Max-plus matrix multiplication is associative.
-/


/-! ## Commutativity and Associativity of Shared Parallel -/



/-! ## Concrete Examples -/

/-
A simple 2-stage pipeline: two scalar event graphs with delays 3 and 5.
    Series composition yields delay 8 = 3 + 5 (tropical multiplication).
-/
/-
Fork-join: two parallel paths with delays 3 and 5.
    Shared parallel composition yields delay 5 = max(3, 5).
-/
end TropicalEventGraph


